#!/bin/bash

travis_wait() {
  local timeout="${1}"

  if [[ "${timeout}" =~ ^[0-9]+$ ]]; then
    shift
  else
    timeout=20
  fi

  local cmd=("${@}")
  local log_file="travis_wait_${$}.log"

  "${cmd[@]}" &>"${log_file}" &
  local cmd_pid="${!}"

  travis_jigger "${!}" "${timeout}" "${cmd[@]}" &
  local jigger_pid="${!}"
  local result

  {
    wait "${cmd_pid}" 2>/dev/null
    result="${?}"
    ps -p"${jigger_pid}" &>/dev/null && kill "${jigger_pid}"
  }

  if [[ "${result}" -eq 0 ]]; then
    printf "\\n${ANSI_GREEN}The command %s exited with ${result}.${ANSI_RESET}\\n" "${cmd[*]}"
  else
    printf "\\n${ANSI_RED}The command %s exited with ${result}.${ANSI_RESET}\\n" "${cmd[*]}"
  fi

  echo -e "\\n${ANSI_GREEN}Log:${ANSI_RESET}\\n"
  cat "${log_file}"

  return "${result}"
}

travis_jigger() {
  local cmd_pid="${1}"
  shift
  local timeout="${1}"
  shift
  local count=0

  echo -e "\\n"

  while [[ "${count}" -lt "${timeout}" ]]; do
    count="$((count + 1))"
    echo -ne "Still running (${count} of ${timeout}): ${*}\\r"
    sleep 60
  done

  echo -e "\\n${ANSI_RED}Timeout (${timeout} minutes) reached. Terminating \"${*}\"${ANSI_RESET}\\n"
  kill -9 "${cmd_pid}"
}

travis_retry() {
  local result=0
  local count=1
  while [[ "${count}" -le 3 ]]; do
    [[ "${result}" -ne 0 ]] && {
      echo -e "\\n${ANSI_RED}The command \"${*}\" failed. Retrying, ${count} of 3.${ANSI_RESET}\\n" >&2
    }
    "${@}" && { result=0 && break; } || result="${?}"
    count="$((count + 1))"
    sleep 1
  done

  [[ "${count}" -gt 3 ]] && {
    echo -e "\\n${ANSI_RED}The command \"${*}\" failed 3 times.${ANSI_RESET}\\n" >&2
  }

  return "${result}"
}
travis_fold() {
  local action="${1}"
  local name="${2}"
  echo -en "travis_fold:${action}:${name}\\r${ANSI_CLEAR}"
}
