# alltarkies

Enumerate all inclusion-minimal (prime) autarkies of a CNF formula, using
[CaDiCaL](https://github.com/arminbiere/cadical) as the SAT engine.

An autarky is a partial assignment that satisfies every clause it touches.
A prime autarky is one with no proper non-empty sub-autarky. Every non-empty
autarky contains a prime one, and the union of compatible autarkies is again
an autarky.

## Build

Requires a CaDiCaL source/build tree next to this repository:

```
git clone https://github.com/arminbiere/cadical
cd cadical && ./configure && make -j
cd ../alltarkies && make
```

## Usage

```
./alltarkies formula.cnf[.xz] [seed]
```

- Input is DIMACS CNF; `.xz` files are decompressed on the fly. The variable
  count is taken from the `p cnf` header line.
- An optional integer `seed` enables shuffled greedy-drop order (for
  randomization); without it a random seed is used.
- Ctrl-C (SIGINT) aborts the search gracefully and still prints partial
  results and statistics.

## Output

One line per prime autarky, both during the run and in a final list:

```
autarky 3: 5 -12 40
```

meaning variables 5 and 40 assigned true, variable 12 assigned false. Lines
starting with `c` are comments, including final statistics (solver calls,
greedy/SAT-based minimization removals, root-fixed pruning, decomposition
counts, total autarkies).

## How it works

1. **Encoding.** Each variable v gets two literals `T_v` (assigned true) and
   `F_v` (assigned false) with at-most-one-polarity clauses; each clause j
   gets a `sat_j` literal so that any model of the encoding is an autarky of
   the input CNF, plus a non-triviality clause.
2. **Outer loop.** Solve, harvest all prime sub-autarkies of the model, then
   add a blocking clause per harvested prime so it is never found again;
   repeat until UNSAT.
3. **Harvest (MARCO-style).** Given a witness, first try a cheap
   decomposition: union-find over touched clauses, merging only variables
   whose literals have opposite truth value in the same clause (a falsified
   literal depends on a satisfying one). If the witness splits into pieces
   that are each autarkies, minimize each piece separately. Otherwise
   minimize the whole witness. Then branch by forcing each variable of the
   reported prime(s) unassigned — every incomparable prime misses such a
   variable and is found in that branch.
4. **Minimization.** A fixpoint greedy pass (no solver calls), then
   jump-until-UNSAT: each SAT solve jumps to a strictly smaller sub-autarky,
   and UNSAT certifies inclusion-minimality.

All queries are assumption/constraint-based (auto-retracted after each
solve); the only permanent clauses are the encoding and the blocking
clauses. Worst-case region splitting is exponential, which is inherent —
there can be exponentially many prime autarkies below one model.

## Files

- `alltarkies.cpp` — the whole tool (single file)
- `Makefile` — build against `../cadical`
- `test.cnf` — example input (49112 variables, 1526724 clauses)
