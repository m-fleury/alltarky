// ji-autarkies.cpp — enumerate ALL autarkies of a CNF with a SAT solver and
// report the join-irreducible ones.
//
// Fresh implementation of the "enumerate + cheap union-find minimization +
// blocking clauses, then filter for join-irreducibility" approach:
//
//   1. Encoding. Each variable v gets polarity literals T(v), F(v) (with an
//      at-most-one clause) and an assigned flag A(v) with A(v) <-> T(v) or
//      F(v). Each clause C gets a satisfied flag S(C) with, for every
//      literal l in C, (opp(l) or S(C)) and (not S(C) or all pol(l)), where
//      opp(l) is the opposite polarity flag: a falsified literal forces
//      S(C), which forces a satisfied literal.
//      So the A/T/F part of any model is exactly an autarky, plus a
//      non-triviality clause (some A(v)).
//   0. Preprocessing. Count literal occurrences. Variables absent from the
//      formula (neither polarity appears) are free: both polarity singletons
//      are join-irreducible autarkies and any larger autarky containing one
//      is a non-trivial union, so such variables are forbidden in the
//      encoding and reported as singleton JIs directly. (A merely absent
//      literal is not excludable: its opposite may satisfy a touched clause,
//      so larger join-irreducibles can contain it.) The most frequent
//      literal is remembered as a union-find hub.
//   2. Enumeration. Solve; each model is an autarky. First minimize the
//      model directly with solver-based dropping: a literal is droppable
//      iff the encoding stays SAT with the rest of the autarky assumed, it
//      unassigned, and all other variables pinned unassigned; greedy dropping
//      to a fixpoint yields a prime autarky.
//      Then cheap-minimize the result with union-find over the touched
//      clauses: in each clause that has a falsified literal, merge the
//      variables of all its falsified and satisfied literals (they have
//      opposite truth values there), and merge the falsified variable with
//      the most frequent literal's variable, so the core stays in one
//      component and only satisfied-only variables can split off. Every
//      connected component is itself an autarky, so a model with several
//      components decomposes into smaller autarkies.
//   3. Blocking. Add a blocking clause per found autarky that forbids
//      exactly that partial assignment (negated polarity literals for its
//      variables, A(v) for all others), so supersets survive and the loop
//      is exhaustive; repeat until UNSAT, then every autarky was seen.
//   4. Join-irreducibles. An autarky X is join-irreducible iff it is not
//      the union of strictly smaller autarkies, i.e. the union of all
//      autarkies Y < X from the full list is a proper subset of X.
//
// Build (against a CaDiCaL source/build tree next to this repository):
//   g++ -O2 -std=c++17 -I ../cadical/src ji-autarkies.cpp \
//       ../cadical/build/libcadical.a -o ji-autarkies
//
// Usage:
//   ./ji-autarkies formula.cnf[.xz] [--all] [--report]
//
// Output: comment lines with statistics, then one line per join-irreducible
// autarky in DIMACS literal format ("ji k: l1 l2 ... 0"); --all additionally
// lists every enumerated autarky, --report shows the SAT solver's progress
// reports (off by default).

#include <cadical.hpp>

#include <algorithm>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <set>
#include <string>
#include <vector>

static volatile sig_atomic_t interrupted = 0;
static void on_sigint (int) { interrupted = 1; }

struct Formula {
  int n = 0;
  std::vector<std::vector<int>> clauses;
};

static Formula read_dimacs (FILE * in) {
  Formula F;
  std::vector<int> cur;
  auto end_clause = [&] {
    if (!cur.empty ()) {
      F.clauses.push_back (cur);
      cur.clear ();
    }
  };
  int c;
  while ((c = fgetc (in)) != EOF) {
    if (c == 'c' || c == '%') {
      while (c != EOF && c != '\n') c = fgetc (in);
      continue;
    }
    if (c == 'p') {
      char line[256];
      if (!fgets (line, sizeof line, in)) break;
      int n = 0, m = 0;
      if (sscanf (line, " cnf %d %d", &n, &m) == 2 && n > F.n) F.n = n;
      continue;
    }
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r') continue;
    ungetc (c, in);
    long l;
    if (fscanf (in, "%ld", &l) != 1) break;
    if (l == 0) {
      end_clause ();
      continue;
    }
    int v = l > 0 ? (int) l : (int) -l;
    if (v > F.n) F.n = v;
    cur.push_back ((int) l);
  }
  end_clause ();
  return F;
}

typedef std::vector<uint64_t> Bits;

static inline void set_lit (Bits & b, int l) {
  int idx = l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1;
  b[idx >> 6] |= 1ull << (idx & 63);
}

static inline bool get_lit (const Bits & b, int l) {
  int idx = l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1;
  return (b[idx >> 6] >> (idx & 63)) & 1ull;
}

static bool is_subset (const Bits & y, const Bits & x) {
  for (size_t w = 0; w < x.size (); w++)
    if (y[w] & ~x[w]) return false;
  return true;
}

static void print_autarky (const char * tag, size_t k, const Bits & b, int n) {
  printf ("%s %zu:", tag, k);
  for (int v = 1; v <= n; v++) {
    if (get_lit (b, v)) printf (" %d", v);
    if (get_lit (b, -v)) printf (" %d", -v);
  }
  printf (" 0\n");
}

int main (int argc, char ** argv) {
  const char * path = 0;
  bool print_all = false, report = false;
  for (int i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "--all"))
      print_all = true;
    else if (!strcmp (argv[i], "--report"))
      report = true;
    else
      path = argv[i];
  }
  if (!path) {
    fprintf (stderr, "usage: %s formula.cnf[.xz] [--all] [--report]\n",
             argv[0]);
    return 1;
  }
  signal (SIGINT, on_sigint);

  FILE * in;
  bool piped = false;
  if (strlen (path) > 3 && !strcmp (path + strlen (path) - 3, ".xz")) {
    std::string cmd = std::string ("xz -dc '") + std::string (path) + std::string ("'");
    in = popen (cmd.c_str (), "r");
    piped = true;
  } else {
    in = fopen (path, "r");
  }
  if (!in) {
    fprintf (stderr, "cannot open %s\n", path);
    return 1;
  }
  Formula F = read_dimacs(in);
  printf ("c dimacs read");
  if (piped)
    pclose (in);
  else
    fclose (in);

  int n = F.n;
  size_t m = F.clauses.size ();
  printf ("c formula: %d variables, %zu clauses\n", n, m);
  if (n == 0) {
    printf ("c empty formula, no non-empty autarky\n");
    return 0;
  }

  // Preprocessing: count literal occurrences. A variable that does not
  // appear in the formula at all (occ(+v) == occ(-v) == 0) is free: both
  // {+v} and {-v} are join-irreducible autarkies, and any larger autarky
  // containing one of them is a non-trivial union (removing it touches and
  // satisfies nothing). Such variables are forbidden in the encoding and
  // reported as singleton JIs directly. A merely absent literal a
  // (occ(a) == 0, occ(-a) > 0) only implies that {-a} is a singleton autarky;
  // it is NOT excludable, because -a may satisfy a touched clause, so larger
  // join-irreducibles may contain it. The most frequent literal is used as
  // the union-find hub below.
  std::vector<long> occ (2 * (size_t) n + 1, 0);
  for (const auto & cl : F.clauses)
    for (int l : cl) occ[l + n]++;
  int top_lit = 0;
  long top_cnt = 0;
  size_t free_cnt = 0, pure_cnt = 0;
  std::vector<int> free_lits;
  for (int v = 1; v <= n; v++) {
    if (occ[v + n] == 0 && occ[-v + n] == 0) {
      free_lits.push_back (v);
      free_lits.push_back (-v);
      free_cnt += 2;
    } else if (occ[v + n] == 0 || occ[-v + n] == 0)
      pure_cnt++;
  }
  for (int l = -n; l <= n; l++) {
    if (l == 0) continue;
    if (occ[l + n] > top_cnt) {
      top_cnt = occ[l + n];
      top_lit = l;
    }
  }
  int top_var = top_lit ? (top_lit > 0 ? top_lit : -top_lit) : 0;
  printf ("c preprocessing: %zu free literals (%zu unused variables), %zu "
          "pure literals, most frequent literal %d (%ld occurrences)\n",
          free_cnt, free_cnt / 2, pure_cnt, top_lit, top_cnt);

  // SAT encoding of the autarky property.
  auto T = [&] (int v) { return 3 * (v - 1) + 1; };
  auto FL = [&] (int v) { return 3 * (v - 1) + 2; };
  auto AS = [&] (int v) { return 3 * (v - 1) + 3; };
  auto pol = [&] (int l) { return l > 0 ? T (l) : FL (-l); };
  int s_base = 3 * n;
  auto S = [&] (size_t c) { return s_base + (int) c + 1; };

  CaDiCaL::Solver solver;
  solver.set ("report", report ? 1 : 0); // --report: show SAT solver progress
  for (int v = 1; v <= n; v++) {
    solver.add (-T (v));
    solver.add (-FL (v));
    solver.add (0); // at most one polarity
    solver.add (-AS (v));
    solver.add (T (v));
    solver.add (FL (v));
    solver.add (0); // A(v) -> T(v) or F(v)
    solver.add (-T (v));
    solver.add (AS (v));
    solver.add (0); // T(v) -> A(v)
    solver.add (-FL (v));
    solver.add (AS (v));
    solver.add (0); // F(v) -> A(v)
  }
  auto opp = [&] (int l) { return l > 0 ? FL (l) : T (-l); };
  for (size_t c = 0; c < m; c++) {
    int s = S (c);
    for (int l : F.clauses[c]) {
      solver.add (-opp (l));
      solver.add (s);
      solver.add (0); // falsified literal (variable assigned, opposite polarity) -> S(C)
    }
    solver.add (-s);
    for (int l : F.clauses[c]) solver.add (pol (l));
    solver.add (0); // S(C) -> some literal satisfied
  }
  for (int v = 1; v <= n; v++) solver.add (AS (v));
  solver.add (0); // non-triviality: at least one variable assigned
  for (int l : free_lits) {
    solver.add (-pol (l));
    solver.add (0); // free literal: never assign it in the encoding
  }
  printf ("c encoding: %d SAT variables\n", s_base + (int) m);

  size_t W = (2 * (size_t) n + 63) / 64;
  std::set<Bits> seen;
  std::vector<Bits> autarkies;
  long solves = 0, decompositions = 0, blocked = 0;
  std::vector<int> parent (n + 1);
  auto find = [&] (int x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  };

  long flippable_drops = 0;

  // Solver-based minimization of an autarky: a literal l is droppable iff
  // the rest is exactly an autarky, i.e. the encoding is SAT with all other
  // literals of the current autarky assumed, l forced unassigned, and all
  // variables outside the current autarky forced unassigned (pinning the
  // whole assignment). On SAT we drop l. Greedy dropping to a fixpoint yields
  // a prime (inclusion-minimal) autarky.
  auto flippable_minimize = [&] (const Bits & b) {
    std::vector<int> lits;
    for (int v = 1; v <= n; v++) {
      if (get_lit (b, v)) lits.push_back (v);
      if (get_lit (b, -v)) lits.push_back (-v);
    }
    for (size_t i = 0; i < lits.size ();) {
      int l = lits[i];
      for (int l2 : lits)
        if (l2 != l) solver.assume (pol (l2));
      solver.assume (-AS (l > 0 ? l : -l)); // try dropping l: unassign it
      for (int v = 1; v <= n; v++)
        if (std::find (lits.begin (), lits.end (), v) == lits.end () &&
            std::find (lits.begin (), lits.end (), -v) == lits.end ())
          solver.assume (-AS (v)); // pin down: nothing else assigned
      int res = solver.solve ();
      solves++;
      if (res == 10) {
        lits.erase (lits.begin () + i); // l not required: drop it
        flippable_drops++;
      } else if (res == 20)
        i++; // l required: keep it
      else {
        fprintf (stderr, "solver failed\n");
        exit (1);
      }
    }
    Bits p (W, 0);
    for (int l : lits) set_lit (p, l);
    return p;
  };

  // Block exactly the partial assignment given by bitset b.
  auto block_exact = [&] (const Bits & b) {
    for (int v = 1; v <= n; v++) {
      if (get_lit (b, v))
        solver.add (-T (v));
      else if (get_lit (b, -v))
        solver.add (-FL (v));
      else
        solver.add (AS (v));
    }
    solver.add (0);
    blocked++;
  };

  while (!interrupted) {
    int res = solver.solve ();
    solves++;
    if (res == 20) break; // UNSAT: all autarkies enumerated
    if (res != 10) {
      fprintf (stderr, "solver failed\n");
      return 1;
    }

    // Extract the autarky from the model.
    std::vector<int> asg (n + 1, 0);
    Bits X (W, 0);
    for (int v = 1; v <= n; v++) {
      if (solver.val (AS (v)) > 0) {
        bool t = solver.val (T (v)) > 0;
        asg[v] = t ? 1 : -1;
        set_lit (X, t ? v : -v);
      }
    }
    if (seen.insert (X).second) autarkies.push_back (X);

    // Minimize the model directly with flippable literals (solver-based),
    // then cheap-minimize the result: union-find decomposition over touched
    // clauses.
    Bits Xm = flippable_minimize (X);
    if (Xm != Bits (W, 0)) { // non-empty: record and block the minimized one
      if (seen.insert (Xm).second) autarkies.push_back (Xm);
      block_exact (Xm);
    }
    for (int v = 1; v <= n; v++) {
      asg[v] = get_lit (Xm, v) ? 1 : (get_lit (Xm, -v) ? -1 : 0);
      parent[v] = v;
    }
    for (const auto & cl : F.clauses) {
      int f0 = 0, s0 = 0;
      for (int l : cl) {
        int v = l > 0 ? l : -l;
        bool lit_true = asg[v] == (l > 0 ? 1 : -1);
        if (asg[v] != 0 && !lit_true) {
          if (!f0) f0 = v;
          else parent[find (v)] = find (f0);
        } else if (asg[v] != 0 && lit_true) {
          if (!s0) s0 = v;
          else parent[find (v)] = find (s0);
        }
      }
      if (f0 && s0) {
        parent[find (f0)] = find (s0);
        // merge every touched clause with the most frequent literal's
        // variable: the core stays in one component, only satisfied-only
        // variables can split off
        if (top_var) parent[find (f0)] = find (top_var);
      }
    }
    std::map<int, Bits> pieces;
    for (int v = 1; v <= n; v++) {
      if (!asg[v]) continue;
      Bits & p = pieces[find (v)];
      if (p.empty ()) p.assign (W, 0);
      set_lit (p, asg[v] > 0 ? v : -v);
    }
    if (pieces.size () > 1) {
      decompositions++;
      for (auto & kv : pieces) {
        if (seen.insert (kv.second).second) autarkies.push_back (kv.second);
        block_exact (kv.second); // block the minimized pieces
      }
    }
    block_exact (X); // block the model itself
  }

  printf ("c enumerated %zu autarkies in %ld solver calls (%ld blocked "
          "clauses, %ld flippable drops, %ld union-find decompositions)%s\n",
          autarkies.size (), solves, blocked, flippable_drops, decompositions,
          interrupted ? " [interrupted, partial]" : "");

  if (print_all) {
    size_t k = 0;
    for (const auto & a : autarkies) print_autarky ("autarky", ++k, a, n);
  }

  // Join-irreducible filter: X is join-irreducible iff the union of all
  // strictly smaller autarkies is a proper subset of X. Free-literal
  // singletons from preprocessing are join-irreducible by construction.
  std::vector<Bits> ji_out;
  for (int l : free_lits) {
    Bits s (W, 0);
    set_lit (s, l);
   ji_out.push_back (s);
  }
  for (size_t i = 0; i < autarkies.size (); i++) {
    const Bits & X = autarkies[i];
    Bits U (W, 0);
    for (size_t j = 0; j < autarkies.size (); j++) {
      if (i == j) continue;
      const Bits & Y = autarkies[j];
      if (Y != X && is_subset (Y, X))
        for (size_t w = 0; w < W; w++) U[w] |= Y[w];
    }
    if (U != X) ji_out.push_back (X);
  }

  // Sanity check: every reported join-irreducible is an autarky of the CNF.
  for (const Bits & X : ji_out) {
    for (const auto & cl : F.clauses) {
      bool touched = false, sat = false;
      for (int l : cl) {
        int v = l > 0 ? l : -l;
        if (!get_lit (X, l)) {
          if (get_lit (X, -l)) touched = true; // literal falsified
        } else
          sat = true;
      }
      if (touched && !sat) {
        fprintf (stderr, "internal error: reported non-autarky\n");
        return 1;
      }
    }
  }

  size_t k = 0;
  for (const Bits & X : ji_out) print_autarky ("ji", ++k, X, n);
  printf ("c join-irreducible autarkies: %zu (%zu free singletons)\n",
          ji_out.size (), free_cnt);
  return 0;
}
