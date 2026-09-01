#!/usr/bin/env bash

set -u

USAGE="usage: $0 FILE [FILE ...]"

if [ $# -eq 0 ]; then
    echo "$USAGE" >&2
    exit 2
fi

if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
    echo "$USAGE"
    exit 0
fi

NON_ASCII="$(printf '[\200-\377]')"

LC_ALL=C grep -Hnb --color=auto -- "$NON_ASCII" "$@"
case $? in
    0) echo "lint-ascii ERR" >&2; exit 1 ;;
    1) echo "lint-ascii OK" ;;
    *) echo "lint-ascii ERR grep ERR" >&2; exit 2 ;;
esac
