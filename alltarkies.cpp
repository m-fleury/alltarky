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
//     - at harvest time, split the witness per assignment by union-find over
//       the touched clauses, merging only opposite-value variable pairs (no
//       precomputation at load); if each piece is an autarky, minimize every
//       piece separately, else minimize the whole witness to a minimal
//       autarky mu (SAT-based, see below);
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
#include <csignal>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {

// SIGINT handling: the handler only sets a flag (async-signal-safe); the
// solver is aborted through a terminator, and the loops check the flag to
// unwind so that the final statistics are still printed.
volatile std::sig_atomic_t sigint_received = 0;
void handle_sigint (int) { sigint_received = 1; }
struct SigintTerminator : CaDiCaL::Terminator {
  bool terminate () override { return sigint_received != 0; }
};
SigintTerminator sigint_terminator;

struct Clause { std::vector<int> lits; };

// run statistics, printed at the end
struct Stats {
  long sat_calls = 0, unsat_calls = 0;  // solver.solve() results
  long greedy_removed = 0;              // variables dropped by greedy_shrink
  long sat_removed = 0;                 // variables dropped by minimize_sat jumps
  long fixed_pruned = 0;                // drop attempts / branches skipped (root-fixed)
  long fixed_vars = 0;                  // variables root-fixed at the last outer solve
  long decomp_witnesses = 0;            // witnesses split by decompose
  long decomp_pieces = 0;               // pieces those witnesses split into
};

// ------------------------------------------------------------ alltarkies

class alltarkies {

  // ------------------------------------------------------------ state
  int n = 0;                            // number of CNF variables
  int m = 0;                            // number of CNF clauses
  std::vector<Clause> F;                // the CNF
  CaDiCaL::Solver solver;               // holds the autarky encoding
  bool shuffle = false;                 // shuffle greedy drop order (seeded)
  std::mt19937 rng;
  Stats st;
  std::set<std::string> reported;       // keys of reported autarkies
  std::vector<std::vector<int>> all_autarkies;
  long found = 0;

public:
  bool ok = false;                      // input loaded successfully

  alltarkies (const std::string & fname, bool shuffle, unsigned seed);
  int run ();

private:
  // ---------------------------------------------------------- DIMACS
  static std::vector<Clause> parse_dimacs (std::istream & in, int & nvars) {
    std::vector<Clause> F;
    std::string line;
    std::vector<int> cur;
    nvars = 0;
    while (std::getline (in, line)) {
      if (line.empty () || line[0] == 'c') continue;
      if (line[0] == 'p') {           // honor the declared variable count
        std::istringstream iss (line);
        std::string tag, cnf;
        int nv = 0, mc = 0;
        iss >> tag >> cnf >> nv >> mc;
        if (nv > nvars) nvars = nv;
        continue;
      }
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

  bool load (const std::string & fname);
  void encode ();

  // ------------------------------------------------- literal helpers
  // T_v = 2v-1 ("v assigned true"), F_v = 2v ("v assigned false"),
  // sat_j = 2n+j ("clause j satisfied").
  int T (int v) const { return 2 * v - 1; }
  int Fv (int v) const { return 2 * v; }
  int sat_lit (int j) const { return 2 * n + j; }

  // read the current model as a partial assignment
  // vals[v] in {-1,0,1}: -1 = unassigned, else truth value.
  std::vector<int> read_model () {
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
  std::string key_of (const std::vector<int> & vals) const {
    std::string s;
    for (int v = 1; v <= n; v++)
      if (vals[v] >= 0) { s += (vals[v] ? "" : "-"); s += std::to_string (v); s += ","; }
    return s;
  }

  // ------------------------------------------------- autarky checking
  bool is_autarky (const std::vector<int> & vals) const {
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

  // ------------------------------------------------------- union-find
  // Split dom(vals) into pieces.  In every clause touched by vals, a literal
  // that is false under vals (the "negative" one) is only kept satisfied by
  // a literal that is true under vals (the "positive" one), so union each
  // falsified variable with every satisfying variable of the same clause --
  // only opposite-value pairs are merged.  Returns true iff there are at
  // least two pieces; each piece is then an autarky (asserted -- a touched
  // clause is satisfied either inside the piece or, via an opposite-value
  // edge, in the same piece), so 'pieces' is a disjoint union of autarkies.
  // Otherwise returns false and the caller falls back to minimizing the
  // witness whole.
  bool decompose (const std::vector<int> & vals,
                  std::vector<std::vector<int>> & pieces) {
    pieces.clear ();
    std::vector<int> parent (n + 1);
    for (int v = 0; v <= n; v++) parent[v] = v;
    auto find = [&] (int x) {
      while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
      return x;
    };
    for (const Clause & C : F) {
      std::vector<int> trues, falses;
      for (int l : C.lits) {
        int v = std::abs (l);
        if (vals[v] < 0) continue;              // only assigned variables
        bool lit_true = (l > 0) == (vals[v] == 1);
        (lit_true ? trues : falses).push_back (v);
      }
      for (int u : falses)
        for (int w : trues) {
          int a = find (u), b = find (w);
          if (a != b) parent[a] = b;
        }
    }
    std::map<int, size_t> root_idx;
    std::vector<std::vector<int>> vars_of;
    for (int v = 1; v <= n; v++) {
      if (vals[v] < 0) continue;
      int r = find (v);
      auto it = root_idx.find (r);
      if (it == root_idx.end ()) {
        root_idx[r] = vars_of.size ();
        vars_of.push_back ({});
        it = root_idx.find (r);
      }
      vars_of[it->second].push_back (v);
    }
    if (vars_of.size () < 2) return false;
    for (const std::vector<int> & vs : vars_of) {
      std::vector<int> p (n + 1, -1);
      for (int v : vs) p[v] = vals[v];
      assert (is_autarky (p));   // opposite-value merging keeps pieces autarkies
      pieces.push_back (std::move (p));
    }
    return true;
  }

  // -------------------------------------------- SAT-based minimization
  // Cheap direct fixpoint greedy (no solver calls).  Never drops the last
  // remaining variable, so the result stays non-trivial.  Dropping v only
  // affects clauses containing v, so those are re-checked via occurrence
  // lists instead of scanning the whole formula.
  void greedy_shrink (std::vector<int> & vals) {
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
      long remaining = 0;
      for (int v = 1; v <= n; v++) if (vals[v] >= 0) remaining++;
      if (remaining <= 1) break;
      if (shuffle) std::shuffle (order.begin (), order.end (), rng);
      for (int v : order) {
        if (remaining <= 1) break;   // never drop the last remaining variable
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
        if (ok) { changed = true; st.greedy_removed++; remaining--; }
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
  std::vector<int> minimize_sat (std::vector<int> vals) {
    greedy_shrink (vals);
    std::vector<int> dom;
    for (;;) {
      if (sigint_received) break;
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
      else { if (res == 20) st.unsat_calls++; dom.clear (); break; }  // UNSAT: minimal
      std::vector<int> jumped = read_model ();        // SAT: jump down
      long after = 0;
      for (int v = 1; v <= n; v++) if (jumped[v] >= 0) after++;
      st.sat_removed += (long) dom.size () - after;
      vals = jumped;
      greedy_shrink(vals);
      dom.clear ();
    }
    return vals;
  }

  // ------------------------------------------------------- harvesting
  // (all minimal sub-autarkies of one model), MARCO-style region
  // recursion.
  //
  // Before minimizing, the witness is split by union-find: in every touched
  // clause, variables whose literals have opposite truth value under the
  // witness are unioned (a falsified literal depends on a satisfying one).
  // If every resulting piece is itself an autarky, the witness is a disjoint
  // union of autarkies and each piece is minimized separately.
  //
  // Region state: 'dropped' = variables forced unassigned; every other
  // variable of dom(alpha) is free between "at alpha's value" and
  // "unassigned" (expressed by assuming the negation of the *opposite*
  // polarity), and variables outside dom(alpha) are forced unassigned.
  void harvest (const std::vector<int> & alpha, std::vector<int> & dropped,
                std::vector<std::vector<int>> & block_list) {
    if (sigint_received) return;         // unwind on SIGINT
    std::vector<int> beta;
    if (dropped.empty ()) {
      beta = alpha;                      // the model itself is a witness
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
      else { if (res == 20) st.unsat_calls++; return; }  // empty region
      beta = read_model ();
    }
    assert (is_autarky (beta));       // cannot happen (encoding)

    // Cheap decomposition: if dom(beta) splits into clause-disjoint pieces
    // that are each autarkies, the witness is a disjoint union of autarkies
    // -- minimize every piece separately instead of minimizing the union and
    // rediscovering the siblings through branching.
    std::vector<std::vector<int>> pieces;
    std::vector<std::vector<int>> mus;
    if (decompose (beta, pieces)) {
      st.decomp_witnesses++;
      st.decomp_pieces += (long) pieces.size ();
      for (const std::vector<int> & p : pieces) mus.push_back (minimize_sat (p));
    }
    else
      mus.push_back (minimize_sat (beta));
    for (const std::vector<int> & mu : mus) {
      bool nonempty = false;
      for (int v = 1; v <= n; v++) if (mu[v] >= 0) { nonempty = true; break; }
      assert (nonempty && is_autarky (mu));  // must be a non-empty autarky
      std::cout << "c after minimization: " << found << " autarkies found so far" << std::endl;
      const std::string k = key_of (mu);
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
    }
    // branch: minimal autarkies incomparable to a reported mu must miss some
    // variable of dom(mu) -- recurse with each such variable dropped (the
    // domains of the mus are pairwise disjoint, so this concatenates them).
    // A root-level fixed variable can never be dropped (the assumption
    // forcing it unassigned contradicts the root fix, so the region is
    // empty), hence its branch is skipped.
    std::vector<int> branch_vars;
    for (const std::vector<int> & mu : mus)
      for (int v = 1; v <= n; v++)
        if (mu[v] >= 0) branch_vars.push_back (v);
    for (int v : branch_vars) {
      if (std::find (dropped.begin (), dropped.end (), v) != dropped.end ()) continue;
      if (solver.fixed (T (v)) == 1 || solver.fixed (Fv (v)) == 1) {
        st.fixed_pruned++;
        continue;
      }
      dropped.push_back (v);
      harvest (alpha, dropped, block_list);
      dropped.pop_back ();
    }
  }
};

// ------------------------------------------------------------ loading

bool alltarkies::load (const std::string & fname) {
  // .xz inputs are decompressed on the fly through `xz -dc`.
  std::ifstream file_in;
  std::istringstream pipe_in;
  std::istream * in = nullptr;
  if (fname.size () >= 3 && fname.compare (fname.size () - 3, 3, ".xz") == 0) {
    std::string cmd = "xz -dc -- '" + fname + "'";
    FILE * pipe = popen (cmd.c_str (), "r");
    if (!pipe) { std::cerr << "cannot pipe " << fname << " through xz" << std::endl; return false; }
    std::string content;
    char buf[4096];
    size_t r;
    while ((r = fread (buf, 1, sizeof (buf), pipe)) > 0) content.append (buf, r);
    if (pclose (pipe) != 0) { std::cerr << "xz failed on " << fname << std::endl; return false; }
    pipe_in.str (content);
    in = &pipe_in;
  } else {
    file_in.open (fname);
    if (!file_in) { std::cerr << "cannot open " << fname << std::endl; return false; }
    in = &file_in;
  }
  F = parse_dimacs (*in, n);
  m = (int) F.size ();
  return true;
}

alltarkies::alltarkies (const std::string & fname, bool sh, unsigned seed)
  : shuffle (sh), rng (seed) {
  solver.connect_terminator (&sigint_terminator);
  ok = load (fname);
  if (ok && n > 0) encode ();
}

// ------------------------------------------------------------ encoding

void alltarkies::encode () {
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
      solver.add (-T (v)); solver.add (sat_lit (j)); solver.add (0);
      solver.add (-Fv (v)); solver.add (sat_lit (j)); solver.add (0);
    }
    // sat_j only if some literal of clause j is made true
    solver.add (-sat_lit (j));
    for (int l : C.lits) solver.add (l > 0 ? T (std::abs (l)) : Fv (std::abs (l)));
    solver.add (0);
  }

  // non-triviality: at least one variable is assigned
  for (int v = 1; v <= n; v++) { solver.add (T (v)); solver.add (Fv (v)); }
  solver.add (0);
}

// ------------------------------------------------------- enumeration

int alltarkies::run () {
  if (n == 0) { std::cout << "c no variables, no non-trivial autarkies" << std::endl; return 0; }

  // -------------------------------------------------- enumeration loop
  for (;;) {
    if (sigint_received) { std::cout << "c interrupted by SIGINT" << std::endl; break; }
    int res = solver.solve ();
    if (res == 10) st.sat_calls++;
    else { if (res == 20) st.unsat_calls++; break; }
    std::vector<int> alpha = read_model ();
    assert (is_autarky (alpha));              // encoding sanity check
    st.fixed_vars = 0;                 // root-fixed variables right now
    for (int v = 1; v <= n; v++)
      if (solver.fixed (T (v)) == 1 || solver.fixed (Fv (v)) == 1) st.fixed_vars++;
    std::vector<std::vector<int>> block_list;
    std::vector<int> dropped;                    // initially nothing dropped
    harvest (alpha, dropped, block_list);
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

  if (sigint_received)
    std::cout << "c run interrupted by SIGINT, partial results" << std::endl;
  std::cout << "c " << found << " minimal autarkies" << std::endl;
  std::cout << "c stats: " << st.sat_calls << " sat, " << st.unsat_calls << " unsat, "
            << (st.sat_calls + st.unsat_calls) << " total solver calls" << std::endl;
  std::cout << "c stats: " << st.greedy_removed << " variables removed greedily, "
            << st.sat_removed << " by sat-based minimization" << std::endl;
  std::cout << "c stats: " << st.fixed_vars << " variables root-fixed at end, "
            << st.fixed_pruned << " drop attempts/branches pruned by fixing" << std::endl;
  std::cout << "c stats: " << st.decomp_witnesses << " witnesses decomposed into "
            << st.decomp_pieces << " pieces" << std::endl;
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

} // namespace

int main (int argc, char ** argv) {
  if (argc < 2) {
    std::cerr << "usage: " << argv[0] << " formula.cnf[.xz] [seed]" << std::endl;
    return 1;
  }
  const bool shuffle = argc > 2;
  const unsigned seed = shuffle ? std::strtoul (argv[2], nullptr, 10)
                                : std::random_device {} ();
  std::signal (SIGINT, handle_sigint);
  alltarkies app (argv[1], shuffle, seed);
  if (!app.ok) return 1;
  return app.run ();
}
