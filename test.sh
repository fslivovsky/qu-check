#!/bin/bash
# Usage: ./test.sh FIRST LAST
# For each seed in FIRST..LAST, generates QCIR instances, solves them with miniQU
# (several configurations, text and binary proofs), checks the proofs with the Lean
# checker (qlrup-check) and the Python reference checker, and compares the verdicts
# with each other and with the solver's exit code. Some text proofs are additionally
# corrupted (a literal or an antecedent of a random derived line is dropped); then the
# two checkers must agree.
FIRST=${1:-1}; LAST=${2:-${FIRST}}
HERE=$(cd "$(dirname "$0")" && pwd)
# MINIQU_REPO: a checkout of https://github.com/fslivovsky/miniQU (for the instance
# generators and the reference checker); MINIQU: the solver binary.
MINIQU_REPO=${MINIQU_REPO:?set MINIQU_REPO to a checkout of miniQU}
TESTS=$MINIQU_REPO/tests
MINIQU=${MINIQU:-$MINIQU_REPO/build/release/bin/miniQU}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cd "$HERE" && lake build qlrup-check > "$TMP/build.log" 2>&1 || { cat "$TMP/build.log"; exit 1; }
LEAN=$(cd "$HERE" && lake env which qlrup-check 2>/dev/null)
[ -x "$LEAN" ] || LEAN=$HERE/.lake/build/bin/qlrup-check
CHUNK=${CHUNK:-}           # optional: run Lean checker with a tiny chunk size
TIMEOUT=${TIMEOUT:-60}

fails=0; total=0; neg=0; skipped=0

verdict() { sed -e 's/^s //' -e 's/: .*//' | head -1; }

lean_check() { "$LEAN" ${CHUNK:+--chunk $CHUNK} "$@" 2>/dev/null | verdict; }

test_instance() {  # name file
    local name=$1 f=$2 k=0
    for cfg in "-dl" "" "-dl -mode=1" "-mode=1"; do
        k=$((k + 1))
        local bin=""; local p=$TMP/p.qlrup
        if [ $(( (k + seed) % 2 )) = 1 ]; then bin=-proof-binary; fi
        timeout $TIMEOUT "$MINIQU" -verb=0 $cfg -proof=$p $bin "$f" > /dev/null 2>&1
        local code=$?
        local want
        case $code in 10) want="VERIFIED TRUE";; 20) want="VERIFIED FALSE";;
            *) skipped=$((skipped + 1)); continue;; esac
        total=$((total + 1))
        local lean py
        lean=$(lean_check "$f" $p)
        py=$(python3 "$TESTS/qlrup_check.py" "$f" $p 2>/dev/null | verdict)
        if [ "$lean" != "$want" ] || [ "$py" != "$want" ]; then
            echo "FAIL $name [$cfg $bin]: solver=$want lean='$lean' python='$py'  (kept in $TMP/fail-$name-$k)"
            mkdir -p "$TMP/fail-$name-$k"; cp "$f" $p "$TMP/fail-$name-$k/"
            trap - EXIT; fails=$((fails + 1))
        fi
        # negative test on text proofs
        if [ -z "$bin" ] && [ $(( (seed + k) % 2 )) = 0 ]; then
            python3 - $p $TMP/m.qlrup $((seed * 10 + k)) <<'PY'
import random, sys
src, dst, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
rng = random.Random(seed)
lines = open(src).read().split('\n')
cand = [i for i, l in enumerate(lines)
        if len(l.split()) > 3 and l.split()[0].isdigit() and l.split()[1] in 'ct']
if not cand:
    open(dst, 'w').write('\n'.join(lines)); sys.exit()
i = rng.choice(cand)
t = lines[i].split()
z = t.index('0', 2)
if rng.random() < 0.5 and z > 2:       # drop a literal
    del t[rng.randrange(2, z)]
else:                                    # drop an antecedent
    ants = list(range(z + 1, len(t) - 1))
    if ants:
        del t[rng.choice(ants)]
lines[i] = ' '.join(t)
open(dst, 'w').write('\n'.join(lines))
PY
            neg=$((neg + 1))
            local l2 p2
            l2=$(lean_check "$f" $TMP/m.qlrup)
            p2=$(python3 "$TESTS/qlrup_check.py" "$f" $TMP/m.qlrup 2>/dev/null | verdict)
            if [ "$l2" != "$p2" ]; then
                echo "FAIL (corrupted) $name [$cfg]: lean='$l2' python='$p2'  (kept in $TMP/negfail-$name-$k)"
                mkdir -p "$TMP/negfail-$name-$k"; cp "$f" $TMP/m.qlrup "$TMP/negfail-$name-$k/"
                trap - EXIT; fails=$((fails + 1))
            fi
        fi
    done
}

for seed in $(seq $FIRST $LAST); do
    python3 "$TESTS/qcir_fuzz.py" $seed > $TMP/a.qcir;               test_instance fuzz$seed $TMP/a.qcir
    python3 "$TESTS/qcir_fuzz.py" $seed --cnf > $TMP/b.qcir;         test_instance cnf$seed $TMP/b.qcir
    python3 "$TESTS/qcir_gen.py" reach $seed 7 12 > $TMP/c.qcir;     test_instance reach$seed $TMP/c.qcir
    python3 "$TESTS/qcir_gen.py" qcnf $seed 6 6 > $TMP/d.qcir;       test_instance qcnf$seed $TMP/d.qcir
    python3 "$TESTS/qcir_gen.py" game $seed 5 > $TMP/e.qcir;         test_instance game$seed $TMP/e.qcir
    python3 "$TESTS/qcir_gen.py" synth $seed 8 > $TMP/g.qcir;        test_instance synth$seed $TMP/g.qcir
done
echo "proofs checked: $total, corrupted proofs compared: $neg, skipped (solver timeout/other exit): $skipped, failures: $fails"
[ $fails = 0 ]
