#!/usr/bin/env bash
set -euo pipefail

FILE="${1:?usage: $0 /path/to/file -- command [args...]}"
shift

# Allow an optional `--` separator for clarity.
if [[ "${1:-}" == "--" ]]; then
  shift
fi

if [[ $# -lt 1 ]]; then
  echo "usage: $0 /path/to/file -- command [args...]"
  exit 2
fi

if [[ ! -e "$FILE" ]]; then
  echo "error: file does not exist: $FILE" >&2
  exit 1
fi

COMMAND=( "$@" )

echo "Watching: $FILE"
echo "Running:  ${COMMAND[*]}"
echo

# -e close_write covers most "save file" events; include move/create/delete for atomic saves.
while inotifywait -q -e close_write,move,create,delete "$FILE"; do
  echo "Change detected @ $(date -Is)"
  "${COMMAND[@]}" || echo "Command exited with code $?" >&2
done