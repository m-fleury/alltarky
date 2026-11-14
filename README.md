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
./alltarkies formula.cnf[.xz] [--generators] [--seeds autarkies.txt] [seed]
```

- `--generators` enumerates the *generators* of the autarky system — the
  join-irreducible autarkies, i.e. autarkies that are not a union of strictly
  smaller autarkies. Every autarky is a union of generators (unlike prime
  autarkies, which are only the inclusion-minimal ones and do not generate
  all autarkies under union). A generator is exactly an inclusion-minimal
  autarky containing some literal l, so the mode runs one MARCO enumeration
  per polarity literal (in a fresh solver each, so blocking clauses do not
  leak across literals): assume l, solve, minimize the witness keeping
  var(l) assigned, report, block its sub-cube, repeat until UNSAT.

- Input is DIMACS CNF; `.xz` files are decompressed on the fly. The variable
  count is taken from the `p cnf` header line.
- `--seeds autarkies.txt` reads known autarkies, one per line in DIMACS
  literal format (`x3 -x5 0`). Each seed is verified to be an autarky of the
  formula (invalid ones are skipped with a warning), minimized to a prime,
  reported, and blocked before enumeration starts — useful when comparing
  against autarkies a SAT solver already found.
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
greedy/SAT-based minimization removals, root-fixed and assumption-propagation
pruning, decomposition counts, total autarkies).

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
5. **Propagation pruning.** Before every region/minimization query the
   assumptions are propagated once (`propagate` + `implied`): a conflict
   answers the query UNSAT without a full solve, and every propagated literal
   holds in all models of the query, so its variable can never be dropped
   there — this prunes harvest branches and shrinks the minimization
   constraint, generalizing the root-level `fixed` pruning.

All queries are assumption/constraint-based (auto-retracted after each
solve); the only permanent clauses are the encoding and the blocking
clauses. Worst-case region splitting is exponential, which is inherent —
there can be exponentially many prime autarkies below one model.

## Files

- `alltarkies.cpp` — the whole tool (single file)
- `ji-autarkies.cpp` — alternative fresh implementation: enumerates *all*
  autarkies (SAT encoding + exact blocking clauses, exhaustive until UNSAT),
  each witness is first minimized with solver-based dropping (a literal is
  dropped iff the autarky without it is still an autarky, a pinned SAT query;
  greedy dropping yields a prime autarky), then cheap union-find
  minimization/decomposition (touched clauses are merged, and every touched
  clause is also merged with the most frequent literal's variable as a hub),
  then filters the full list for the
  join-irreducible autarkies (an autarky X is join-irreducible iff the union
  of all strictly smaller autarkies is a proper subset of X). Preprocessing
  counts literal occurrences: variables absent from the formula are free
  (both polarity singletons are join-irreducible and are reported directly,
  the variable is excluded from the encoding). Build with `make ji`, run
  `./ji-autarkies formula.cnf[.xz] [--all] [--report]` (`--report` shows the
  SAT solver's progress reports, off by default). Note the exhaustive
  enumeration is only feasible for small formulas — the number of autarkies
  can be exponential.
- `Makefile` — build against `../cadical`
- `test.cnf` — example input (49112 variables, 1526724 clauses)
