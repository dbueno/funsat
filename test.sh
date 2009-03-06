if test -n "$1"; then
    DSAT="$1"
else
    DSAT="./dist/build/funsat/funsat"
fi

echo 1>&2 "Using '$DSAT'"

# record feature set
echo "SAT solver features under test:"
$DSAT --print-features

ABORT="error, exiting without completing tests"
FAILURE="test failure"

echo "Testing quick check properties"
time $DSAT --verify 2>&1

NSAT=1000
echo "Testing $NSAT satisfiable problems (20 vars)"
time ls -1 ./tests/problems/uf20/*.cnf | head -$NSAT | while read F; do $DSAT $F; done 2>&1 | grep -1 -i "unsatisfiable\\|assertion"

NSAT=1000
echo "Testing $NSAT satisfiable problems (50 vars)"
time ls -1 ./tests/problems/uf50/*.cnf | head -$NSAT | while read F; do $DSAT $F; done 2>&1 | grep -1 -i "unsatisfiable\\|assertion"

NUNSAT=1000
echo "Testing $NUNSAT unsatisfiable problems (50 vars)"
time ls -1 ./tests/problems/uuf50/*.cnf | head -$NUNSAT | while read F; do $DSAT $F; done 2>&1 | grep -1 -i "satisfiable[:]\\|assertion"

