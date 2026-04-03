from __future__ import annotations
import queue
import subprocess
import threading
from typing import Callable

class AgdaProcess:
    """Thin interaction wrapper around `agda --interaction-json`.

    Preconditions:
    - `agda` is installed and available on PATH.
    - callers send complete one-line interaction commands.

    Invariants:
    - this wrapper does not accept proofs; it only transports protocol messages.
    - process liveness is checked before writing to stdin.

    Postconditions:
    - startup failures are surfaced as RuntimeError.
    - writes to a dead process are surfaced as RuntimeError, not BrokenPipeError.
    """

    def __init__(
        self,
        file_path: str,
        observer: Callable[[dict[str, object]], None] | None = None,
    ):
        self.file_path = str(file_path)
        self._observer = observer
        try:
            self.proc = subprocess.Popen(
                ["agda", "--interaction-json"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
        except OSError as exc:
            raise RuntimeError("failed to start `agda --interaction-json`") from exc
        self._queue: "queue.Queue[str]" = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()
        if self._observer is not None:
            self._observer({
                "event": "process_start",
                "file": self.file_path,
                "pid": self.proc.pid,
            })

    def _read_loop(self) -> None:
        assert self.proc.stdout is not None
        for line in self.proc.stdout:
            line = line.rstrip("\n")
            if line == "JSON>":
                continue
            if line.startswith("JSON> "):
                line = line[6:]
            if line:
                self._queue.put(line)
        if self._observer is not None:
            self._observer({
                "event": "process_exit",
                "file": self.file_path,
                "returncode": self.proc.poll(),
            })

    def send(self, cmd: str) -> None:
        if self.proc.poll() is not None:
            raise RuntimeError(f"Agda interaction process exited with code {self.proc.returncode}")
        if self.proc.stdin is None:
            raise RuntimeError("Agda stdin unavailable")
        try:
            self.proc.stdin.write(cmd + "\n")
            self.proc.stdin.flush()
        except BrokenPipeError as exc:
            raise RuntimeError("Agda interaction pipe closed during send") from exc

    def recv(self, timeout: float = 0.2) -> str | None:
        try:
            return self._queue.get(timeout=timeout)
        except queue.Empty:
            return None

    def drain(self, timeout: float = 0.2) -> list[str]:
        out: list[str] = []
        while True:
            msg = self.recv(timeout=timeout)
            if msg is None:
                break
            out.append(msg)
        return out

    def send_and_collect(self, cmd: str, timeout: float = 0.2) -> list[str]:
        self.send(cmd)
        return self.drain(timeout=timeout)

    def close(self) -> None:
        if self.proc.poll() is not None:
            if self._observer is not None:
                self._observer({
                    "event": "process_close",
                    "file": self.file_path,
                    "returncode": self.proc.returncode,
                })
            return
        if self.proc.stdin is not None:
            try:
                self.proc.stdin.close()
            except OSError:
                pass
        self.proc.terminate()
        try:
            self.proc.wait(timeout=0.5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=0.5)
        if self._observer is not None:
            self._observer({
                "event": "process_close",
                "file": self.file_path,
                "returncode": self.proc.returncode,
            })
