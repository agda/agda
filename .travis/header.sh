#!/bin/bash
# The following bash functions are from
# https://github.com/travis-ci/travis-build/tree/master/lib/travis/build/bash

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

travis_nanoseconds() {
  local cmd='date'
  local format='+%s%N'

  if hash gdate >/dev/null 2>&1; then
    cmd='gdate'
  elif [[ "${TRAVIS_OS_NAME}" == osx ]]; then
    format='+%s000000000'
  fi

  "${cmd}" -u "${format}"
}

travis_time_start() {
  TRAVIS_TIMER_ID="$(printf %08x $((RANDOM * RANDOM)))"
  TRAVIS_TIMER_START_TIME="$(travis_nanoseconds)"
  export TRAVIS_TIMER_ID TRAVIS_TIMER_START_TIME
  echo -en "travis_time:start:$TRAVIS_TIMER_ID\\r${ANSI_CLEAR}"
}

travis_time_finish() {
  local result="${?}"
  local travis_timer_end_time
  local event="${1}"
  travis_timer_end_time="$(travis_nanoseconds)"
  local duration
  duration="$((travis_timer_end_time - TRAVIS_TIMER_START_TIME))"
  echo -en "travis_time:end:${TRAVIS_TIMER_ID}:start=${TRAVIS_TIMER_START_TIME},finish=${travis_timer_end_time},duration=${duration},event=${event}\\r${ANSI_CLEAR}"
  return "${result}"
}

fold_cmd() {
  local name="${1}"
  shift
  local cmd=("${@}")
  travis_fold start ${name}
  "${cmd[@]}"
  local result="${?}"
  travis_fold end ${name}
  return "${result}"
}

title() {
  echo -e "\033[1m\033[33m${1}\033[0m"
}


subtitle() {
  echo -e "\033[34m${1}\033[0m"
}

# TODO: rewrite this function
fold_timer_cmd() {
  local name="${1}"
  local title="${2}"
  shift 2
  local cmd=("${@}")
  echo -en "travis_fold:start:${name}\\r${ANSI_CLEAR}"
  title "${title}"
  travis_time_start
  "${cmd[@]}"
  local result="${?}"
  travis_time_finish
  echo -en "travis_fold:end:${name}\\r${ANSI_CLEAR}"
  return "${result}"
}
