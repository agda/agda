from __future__ import annotations

import gc
import os


def rss_bytes() -> int:
    try:
        import psutil  # type: ignore

        return psutil.Process(os.getpid()).memory_info().rss
    except Exception:
        try:
            with open("/proc/self/statm", "r", encoding="utf-8") as handle:
                pages = int(handle.read().split()[1])
            return pages * os.sysconf("SC_PAGE_SIZE")
        except Exception:
            return 0


def rss_mb() -> float:
    return round(rss_bytes() / (1024 * 1024), 2)


def cleanup() -> None:
    gc.collect()
