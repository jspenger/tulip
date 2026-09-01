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

ADD_BLACKLIST="add +(field|loadpath|ml|morphism|parametric|rec|relation|ring|search|setoid|zify)"

SET_BLACKLIST="set +(allow|definitional|guard|implicit|nested|positivity|universe)"

BLACKLIST="$ADD_BLACKLIST
$SET_BLACKLIST
admit
arguments
attributes
axiom
back
bypass_check
canonical
class
coercion
conjecture
constraint
context
declare
derive
drop
existing
export
extract
generalizable
give_up
global
hint
hypothes
implicit
import
include
infix
instance
load
ltac
ml +module
ml +path
native_compute
notation
obligation
opaque
parameter
primitive
program
redirect
register
require
reset
restart
rewrite +rule
scope
strategy
structure
symbol
transparent
undo
universe
unset
variable
vm_compute"

LC_ALL=C grep -HniEb --color=auto -- "$BLACKLIST" "$@"
case $? in
    0) echo "lint-blacklist ERR" >&2; exit 1 ;;
    1) echo "lint-blacklist OK" ;;
    *) echo "lint-blacklist ERR grep ERR" >&2; exit 2 ;;
esac
