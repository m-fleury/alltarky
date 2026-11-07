// autarkies.cpp — enumerate all minimal (prime) autarkies of a CNF with CaDiCaL.
//
// Build (against a CaDiCaL source/build tree):
//   git clone https://github.com/arminbiere/cadical
//   cd cadical && ./configure && make -j
//   g++ -O2 -std=c++17 -I cadical/src autarkies.cpp cadical/build/libcadical.a -o autarkies
//
// Usage:
//   ./autarkies formula.cnf [seed]
//
// One minimal autarky per line: "autarky k: x3=T x5=F ...".
//
// Outer loop: solve the autarky encoding, then *harvest* ALL minimal
// sub-autarkies of the found model before blocking, MARCO-style:
//
//   harvest (alpha, dropped):
//     - query (under assumptions) the region of sub-assignments of alpha
//       in which every variable of 'dropped' is unassigned; UNSAT -> return;
//     - minimize the witness to a minimal autarky mu (SAT-based, see below);
//     - report mu, then branch on every v in dom(mu): recurse with v dropped.
//
// Completeness of the harvest: any minimal autarky gamma below alpha either
// equals mu, or is incomparable to it, in which case gamma misses some
// v in dom(mu) (otherwise gamma would strictly extend the autarky mu and
// could not be minimal), and is then found in the branch that drops v.
//
// SAT-based minimization (deletion-based, MUS-style): for every variable v
// of the current autarky, ask under assumptions whether a sub-autarky
// exists that drops v.  SAT -> jump to the strictly smaller witness; UNSAT
// -> v is essential.  One pass over the domain yields an inclusion-minimal
// autarky; earlier UNSAT proofs stay valid since it only shrinks.
//
// All queries are assumption-based (per-solve, auto-retracted); the only
// permanent clauses are the sub-cube blocking clauses of the reported
// minimal autarkies.  Region splitting can in the worst case explore
// exponentially many nodes (inherent: there can be exponentially many
// minimal autarkies below one model); duplicates are filtered by key.

#if __has_include(<cadical.hpp>)
#include <cadical.hpp>
#elif __has_include(<../cadical/src/solver.hpp>)
#include <../cadical/src/solver.hpp>
#else
#include "../cadical/src/cadical.hpp"
#endif

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {

struct Clause { std::vector<int> lits; };

// run statistics, printed at the end
struct Stats {
  long sat_calls = 0, unsat_calls = 0;  // solver.solve() results
  long greedy_removed = 0;              // variables dropped by greedy_shrink
  long sat_removed = 0;                 // variables dropped by minimize_sat jumps
  long fixed_pruned = 0;                // drop attempts / branches skipped (root-fixed)
  long fixed_vars = 0;                  // variables root-fixed at the last outer solve
};

// ---------------------------------------------------------------- DIMACS

std::vector<Clause> parse_dimacs (std::istream & in, int & nvars) {
  std::vector<Clause> F;
  std::string line;
  std::vector<int> cur;
  nvars = 0;
  while (std::getline (in, line)) {
    if (line.empty () || line[0] == 'c' || line[0] == 'p') continue;
    std::istringstream iss (line);
    int x;
    while (iss >> x) {
      if (x == 0) {
        if (!cur.empty ()) { F.push_back ({cur}); cur.clear (); }
      } else {
        cur.push_back (x);
        int v = std::abs (x);
        if (v > nvars) nvars = v;
      }
    }
  }
  if (!cur.empty ()) F.push_back ({cur});
  return F;
}

// ------------------------------------------------------- autarky checking
// vals[v] in {-1,0,1}: -1 = unassigned, else truth value.

bool is_autarky (const std::vector<Clause> & F, const std::vector<int> & vals) {
  for (const Clause & C : F) {
    bool touched = false, sat = false;
    for (int l : C.lits) {
      int a = vals[std::abs (l)];
      if (a >= 0) {
        touched = true;
        if ((l > 0) == (a == 1)) sat = true;
      }
    }
    if (touched && !sat) return false;
  }
  return true;
}

// ------------------------------------------------------- literal helpers
// T_v = 2v-1 ("v assigned true"), F_v = 2v ("v assigned false"),
// sat_j = 2n+j ("clause j satisfied").

int T (int v) { return 2 * v - 1; }
int Fv (int v) { return 2 * v; }
int sat_lit (int n, int j) { return 2 * n + j; }

// read the current model as a partial assignment
std::vector<int> read_model (CaDiCaL::Solver & solver, int n) {
  std::vector<int> vals (n + 1, -1);
  for (int v = 1; v <= n; v++) {
    bool t = solver.val (T (v)) > 0;
    bool f = solver.val (Fv (v)) > 0;
    if (t && !f) vals[v] = 1;
    else if (f && !t) vals[v] = 0;
  }
  return vals;
}

// canonical key of a partial assignment (for duplicate filtering)
std::string key_of (int n, const std::vector<int> & vals) {
  std::string s;
  for (int v = 1; v <= n; v++)
    if (vals[v] >= 0) { s += (vals[v] ? "" : "-"); s += std::to_string (v); s += ","; }
  return s;
}

// ---------------------------------------------- SAT-based minimization
// Cheap direct fixpoint greedy (no solver calls).  Never drops the last
// remaining variable, so the result stays non-trivial.  Dropping v only
// affects clauses containing v, so those are re-checked via occurrence
// lists instead of scanning the whole formula.
void greedy_shrink (CaDiCaL::Solver & solver,
                    const std::vector<Clause> & F, int n, bool shuffle,
                    std::mt19937 & rng, std::vector<int> & vals, Stats & st) {
  std::vector<std::vector<int>> occ (n + 1);
  for (int j = 0; j < (int) F.size (); j++)
    for (int l : F[j].lits) occ[std::abs (l)].push_back (j);
  for (bool changed = true; changed;) {
    changed = false;
    std::vector<int> order;
    // variables fixed at root level are assigned in every future model and
    // can never be dropped, so do not even try (fixed() is only meaningful
    // after a solve, when root-level propagation has run)
    for (int v = 1; v <= n; v++) {
      if (vals[v] < 0) continue;
      if (solver.fixed (T (v)) == 1 || solver.fixed (Fv (v)) == 1) {
        st.fixed_pruned++;
        continue;
      }
      order.push_back (v);
    }
    if (order.size () <= 1) break;
    if (shuffle) std::shuffle (order.begin (), order.end (), rng);
    for (int v : order) {
      int old = vals[v];
      vals[v] = -1;
      bool ok = true;
      for (int j : occ[v]) {
        const Clause & C = F[j];
        bool touched = false, sat = false;
        for (int l : C.lits) {
          int a = vals[std::abs (l)];
          if (a >= 0) {
            touched = true;
            if ((l > 0) == (a == 1)) {sat = true; break;}
          }
        }
        if (touched && !sat) { ok = false; break; }
      }
      if (ok) { changed = true; st.greedy_removed++; }
      else vals[v] = old;
    }
  }
}

// Jump-until-UNSAT: each round asks with ONE temporary constraint clause
// (CaDiCaL retracts it automatically after 'solve', like assumptions)
// whether a strictly smaller sub-autarky of the current one exists.
//   SAT   -> jump to the smaller witness, re-run the greedy, repeat;
//   UNSAT -> no proper sub-autarky exists: inclusion-minimal, done.
// Total solver calls = number of jumps + 1, instead of one per variable.
std::vector<int> minimize_sat (CaDiCaL::Solver & solver,
                               const std::vector<Clause> & F,
                               int n, bool shuffle, std::mt19937 & rng,
                               std::vector<int> vals, Stats & st) {
  greedy_shrink (solver, F, n, shuffle, rng, vals, st);
  for (;;) {
    std::vector<int> dom;
    for (int v = 1; v <= n; v++) if (vals[v] >= 0) dom.push_back (v);
    if (dom.empty ()) break;
    // assumptions: sub-cube of the current autarky (each domain variable
    // may keep its value or become unassigned; all others stay unassigned)
    for (int u = 1; u <= n; u++) {
      if (vals[u] >= 0) solver.assume (vals[u] ? -Fv (u) : -T (u));
      else { solver.assume (-T (u)); solver.assume (-Fv (u)); }
    }
    // constraint clause: at least one domain variable unassigned, i.e.
    // not at its current value (the opposite polarity is assumed away)
    for (int v : dom) solver.constrain (vals[v] ? -T (v) : -Fv (v));
    solver.constrain (0);
    int res = solver.solve ();
    if (res == 10) st.sat_calls++;
    else { st.unsat_calls++; break; }      // UNSAT: inclusion-minimal
    std::vector<int> jumped = read_model (solver, n);   // SAT: jump down
    long after = 0;
    for (int v = 1; v <= n; v++) if (jumped[v] >= 0) after++;
    st.sat_removed += (long) dom.size () - after;
    vals = jumped;
    greedy_shrink (solver, F, n, shuffle, rng, vals, st);
  }
  return vals;
}

// --------------------------------------------------- harvesting (all
// minimal sub-autarkies of one model), MARCO-style region recursion.
//
// Region state: 'dropped' = variables forced unassigned; every other
// variable of dom(alpha) is free between "at alpha's value" and
// "unassigned" (expressed by assuming the negation of the *opposite*
// polarity), and variables outside dom(alpha) are forced unassigned.
void harvest (CaDiCaL::Solver & solver,
              const std::vector<Clause> & F,
              int n, bool shuffle, std::mt19937 & rng,
              const std::vector<int> & alpha, std::vector<int> & dropped,
              std::set<std::string> & reported,
              std::vector<std::vector<int>> & block_list,
              std::vector<std::vector<int>> & all_autarkies,
              long & found, Stats & st) {
  std::vector<int> beta;
  if (dropped.empty ()) {
    beta = alpha;                        // the model itself is a witness
  } else {
    for (int u = 1; u <= n; u++) {
      if (alpha[u] >= 0) {
        solver.assume (alpha[u] ? -Fv (u) : -T (u));  // sub-cube of alpha
        if (std::find (dropped.begin (), dropped.end (), u) != dropped.end ())
          solver.assume (alpha[u] ? -T (u) : -Fv (u)); // forced unassigned
      } else {
        solver.assume (-T (u));
        solver.assume (-Fv (u));
      }
    }
    int res = solver.solve ();
    if (res == 10) st.sat_calls++;
    else { st.unsat_calls++; return; }   // empty region
    beta = read_model (solver, n);
  }
  if (!is_autarky (F, beta)) return;     // cannot happen (encoding)

  std::vector<int> mu = minimize_sat (solver, F, n, shuffle, rng, beta, st);
  if (!is_autarky (F, mu)) {               // debug: verify found autarky
    std::cerr << "internal error: found assignment is not an autarky" << std::endl;
    std::abort ();
  }
  std::cout << "c after minimization: " << found << " autarkies found so far" << std::endl;
  const std::string k = key_of (n, mu);
  if (!reported.count (k)) {
    reported.insert (k);
    block_list.push_back (mu);
    all_autarkies.push_back (mu);
    found++;
    std::cout << "autarky " << found << ":";
    for (int v = 1; v <= n; v++)
      if (mu[v] >= 0)
        std::cout << " " << (mu[v] ? "" : "-") << v;
    std::cout << std::endl;
  }
  // branch: minimal autarkies incomparable to mu must miss some
  // variable of dom(mu) -- recurse with each such variable dropped.
  // A root-level fixed variable can never be dropped (the assumption
  // forcing it unassigned contradicts the root fix, so the region is
  // empty), hence its branch is skipped.
  for (int v = 1; v <= n; v++) {
    if (mu[v] < 0) continue;
    if (std::find (dropped.begin (), dropped.end (), v) != dropped.end ()) continue;
    if (solver.fixed (T (v)) == 1 || solver.fixed (Fv (v)) == 1) {
      st.fixed_pruned++;
      continue;
    }
    dropped.push_back (v);
    harvest (solver, F, n, shuffle, rng, alpha, dropped,
             reported, block_list, all_autarkies, found, st);
    dropped.pop_back ();
  }
}

} // namespace

int main (int argc, char ** argv) {
  if (argc < 2) {
    std::cerr << "usage: " << argv[0] << " formula.cnf[.xz] [seed]" << std::endl;
    return 1;
  }
  // .xz inputs are decompressed on the fly through `xz -dc`.
  const std::string fname = argv[1];
  std::ifstream file_in;
  std::istringstream pipe_in;
  std::istream * in = nullptr;
  if (fname.size () >= 3 && fname.compare (fname.size () - 3, 3, ".xz") == 0) {
    std::string cmd = "xz -dc -- '" + fname + "'";
    FILE * pipe = popen (cmd.c_str (), "r");
    if (!pipe) { std::cerr << "cannot pipe " << fname << " through xz" << std::endl; return 1; }
    std::string content;
    char buf[4096];
    size_t r;
    while ((r = fread (buf, 1, sizeof (buf), pipe)) > 0) content.append (buf, r);
    if (pclose (pipe) != 0) { std::cerr << "xz failed on " << fname << std::endl; return 1; }
    pipe_in.str (content);
    in = &pipe_in;
  } else {
    file_in.open (fname);
    if (!file_in) { std::cerr << "cannot open " << fname << std::endl; return 1; }
    in = &file_in;
  }

  int n = 0;
  std::vector<Clause> F = parse_dimacs (*in, n);
  const int m = (int) F.size ();
  if (n == 0) { std::cout << "c no variables, no non-trivial autarkies" << std::endl; return 0; }

  std::mt19937 rng (argc > 2 ? std::strtoul (argv[2], nullptr, 10)
                             : std::random_device {} ());
  const bool shuffle = argc > 2;

  // ---------------------------------------------------------- encoding
  CaDiCaL::Solver solver;
  solver.set ("verbose", 0);
  solver.set ("report", 1);
  solver.set ("lucky", 0);
  solver.set ("ilb", 2);

  // at most one polarity per variable
  for (int v = 1; v <= n; v++) { solver.add (-T (v)); solver.add (-Fv (v)); solver.add (0); }

  for (int j = 1; j <= m; j++) {
    const Clause & C = F[j - 1];
    if (C.lits.empty ()) continue;   // empty clause can never be touched
    for (int l : C.lits) {           // touching clause j forces sat_j
      int v = std::abs (l);
      solver.add (-T (v)); solver.add (sat_lit (n, j)); solver.add (0);
      solver.add (-Fv (v)); solver.add (sat_lit (n, j)); solver.add (0);
    }
    // sat_j only if some literal of clause j is made true
    solver.add (-sat_lit (n, j));
    for (int l : C.lits) solver.add (l > 0 ? T (std::abs (l)) : Fv (std::abs (l)));
    solver.add (0);
  }

  // non-triviality: at least one variable is assigned
  for (int v = 1; v <= n; v++) { solver.add (T (v)); solver.add (Fv (v)); }
  solver.add (0);

  std::set<std::string> reported;
  std::vector<std::vector<int>> block_list;
  std::vector<std::vector<int>> all_autarkies;
  long found = 0;
  Stats st;

  // ---------------------------------------------------- enumeration loop
  for (;;) {
    int res = solver.solve ();
    if (res == 10) st.sat_calls++;
    else { st.unsat_calls++; break; }
    std::vector<int> alpha = read_model (solver, n);
    if (!is_autarky (F, alpha)) {                // encoding sanity check
      std::cerr << "internal error: model is not an autarky" << std::endl;
      return 2;
    }
    st.fixed_vars = 0;                 // root-fixed variables right now
    for (int v = 1; v <= n; v++)
      if (solver.fixed (T (v)) == 1 || solver.fixed (Fv (v)) == 1) st.fixed_vars++;
    block_list.clear ();
    std::vector<int> dropped;                    // initially nothing dropped
    harvest (solver, F, n, shuffle, rng, alpha, dropped,
             reported, block_list, all_autarkies, found, st);
    if (block_list.empty ()) break;              // safety net

    // block the sub-cubes of all harvested minimal autarkies: any future
    // autarky must differ on the domain of each of them.  Sound: if another
    // minimal autarky gamma agreed with mu on dom(mu), then gamma <= mu,
    // contradicting mu's minimality unless gamma = mu.
    for (const std::vector<int> & mu : block_list) {
      bool any = false;
      for (int v = 1; v <= n; v++)
        if (mu[v] >= 0) {
          solver.add (mu[v] ? -T (v) : -Fv (v));
          any = true;
        }
      if (!any) continue;
      solver.add (0);
    }
  }

  std::cout << "c " << found << " minimal autarkies" << std::endl;
  std::cout << "c stats: " << st.sat_calls << " sat, " << st.unsat_calls << " unsat, "
            << (st.sat_calls + st.unsat_calls) << " total solver calls" << std::endl;
  std::cout << "c stats: " << st.greedy_removed << " variables removed greedily, "
            << st.sat_removed << " by sat-based minimization" << std::endl;
  std::cout << "c stats: " << st.fixed_vars << " variables root-fixed at end, "
            << st.fixed_pruned << " drop attempts/branches pruned by fixing" << std::endl;
  std::cout << "c stats: " << found << " minimal autarkies" << std::endl;
  std::cout << "c all found autarkies:" << std::endl;
  for (size_t i = 0; i < all_autarkies.size (); i++) {
    std::cout << "autarky " << (i + 1) << ":";
    for (int v = 1; v <= n; v++)
      if (all_autarkies[i][v] >= 0)
        std::cout << " " << (all_autarkies[i][v] ? v : -v);
    std::cout << std::endl;
  }
  return 0;
}