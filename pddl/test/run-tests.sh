#!/bin/bash
# Run the PDDL front end over the test instances shipped with this repository and,
# optionally, over a checkout of https://github.com/aibasel/downward-benchmarks/.
#
# Usage:
#   pddl/test/run-tests.sh [PATH-TO-downward-benchmarks]
#
# Every file is parsed, printed back to PDDL, parsed again and compared (--roundtrip);
# every problem is additionally checked for static well-formedness against its domain
# (--check); the STRIPS test instance is also grounded (--ground) and the small shipped
# instances are solved by the verified planner (--solve).  Files that use
# features outside the supported fragment (derived predicates, numeric fluents, durative
# actions, preferences, ...) are reported as failures with an explanatory message; this is
# intended behaviour.

set -u
cd "$(dirname "$0")/../.." || exit 1
PDDLPARSE=.lake/build/bin/pddlparse

if [ ! -x "$PDDLPARSE" ]; then
  echo "building the parser front end ..."
  lake build pddlparse || exit 1
fi

status=0

echo "== shipped test instances =="
$PDDLPARSE --roundtrip --check \
  pddl/test/transport-lite-domain.pddl pddl/test/transport-lite-problem.pddl || status=1
$PDDLPARSE --roundtrip --check \
  pddl/test/edge-cases-domain.pddl pddl/test/edge-cases-problem.pddl || status=1
$PDDLPARSE --roundtrip --check --ground \
  pddl/test/blocks-lite-domain.pddl pddl/test/blocks-lite-problem.pddl || status=1

echo "== solving the shipped test instances =="
$PDDLPARSE --solve \
  pddl/test/blocks-lite-domain.pddl pddl/test/blocks-lite-problem.pddl || status=1
$PDDLPARSE --solve \
  pddl/test/transport-lite-domain.pddl pddl/test/transport-lite-problem.pddl || status=1

if [ $# -ge 1 ]; then
  bench=$1
  echo "== benchmarks in $bench =="
  for dir in "$bench"/*/; do
    [ -d "$dir" ] || continue
    if [ -f "$dir/domain.pddl" ]; then
      probs=$(ls "$dir"/*.pddl | grep -v '/domain.pddl$')
      # shellcheck disable=SC2086
      $PDDLPARSE --roundtrip --check "$dir/domain.pddl" $probs
    else
      for dom in "$dir"*-domain.pddl; do
        [ -e "$dom" ] || continue
        pre=$(basename "$dom" | sed 's/-domain.pddl//')
        probs=$(ls "$dir$pre"-*.pddl 2>/dev/null | grep -v -- '-domain.pddl$')
        # shellcheck disable=SC2086
        [ -n "$probs" ] && $PDDLPARSE --roundtrip --check "$dom" $probs
      done
    fi
  done
fi

exit $status
