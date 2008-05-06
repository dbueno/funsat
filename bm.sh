DSAT=./dist/build/dsat/dsat
BMFILE=bm-$(gdate +%F.%H%M)

OPTIONS=""

# record feature set
echo "SAT solver features under test:"
$DSAT --print-features $OPTIONS

# NSAT=1000
# echo "Testing $NSAT satisfiable problems (20 vars)"
# time ls -1 ./tests/problems/uf20/*.cnf | head -$NSAT | while read F; do $DSAT $F $OPTIONS; done 2>&1 | grep -1 -i "unsatisfiable\\|assertion"

# NSAT=1000
# echo "Testing $NSAT satisfiable problems (50 vars)"
# time ls -1 ./tests/problems/uf50/*.cnf | head -$NSAT | while read F; do $DSAT $F $OPTIONS; done 2>&1 | grep -1 -i "unsatisfiable\\|assertion"

# NUNSAT=1000
# echo "Testing $NUNSAT unsatisfiable problems (50 vars)"
# time ls -1 ./tests/problems/uuf50/*.cnf | head -$NUNSAT | while read F; do $DSAT $F $OPTIONS; done 2>&1 | grep -1 -i "satisfiable[:]\\|assertion"

