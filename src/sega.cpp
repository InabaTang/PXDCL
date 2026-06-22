#include "sega.hpp"

namespace CaDiCaL {

bool Internal::segaing()
{
    return !xor_full_clause.empty();
}

// Process fully-assigned long XOR clauses (size > 5).
// Recomputes XOR parity from scratch for correctness — the incrementally-
// tracked xor_clause_parity may drift due to complex backtrack/reassign
// patterns.  The tracking is still maintained for bump_near_full_xor().
void Internal::sega()
{
    vector<int> to_process = xor_full_clause;
    xor_full_clause.clear();

    for (int ci : to_process) {
        if (ci < 0 || ci >= (int)long_xor_clauses.size()) continue;
        Clause *c = long_xor_clauses[ci];
        if (c == nullptr) continue;  // clause was deleted by GC
        if (c->garbage || c->size == 0) continue;
        if (c->size != xor_clause_size[ci]) continue;

        // Verify ALL literals are actually assigned (counter may be stale)
        bool all_assigned = true;
        bool xor_parity = false;
        for (int i = 0; i < c->size; i++) {
            int lit = c->literals[i];
            signed char v = val(lit);
            if (!v) { all_assigned = false; break; }
            if (v > 0)
                xor_parity = !xor_parity;
        }
        if (!all_assigned) continue;  // counter was wrong, skip

        if (xor_parity)
            continue;  // satisfied

        // XOR violated: all literals assigned false (even parity).
        conflict = c;
        break;
    }
}

// Boost decision scores for unassigned variables in near-full long XOR
// clauses.  When a clause is >= 60% assigned, its remaining unassigned
// variables get score bumps so the solver focuses on completing XOR constraints.
void Internal::bump_near_full_xor()
{
    for (size_t ci = 0; ci < long_xor_clauses.size(); ci++) {
        Clause *c = long_xor_clauses[ci];
        if (c == nullptr || c->garbage) continue;
        int cnt = xor_clause_counter[ci];
        int sz = xor_clause_size[ci];
        if (cnt * 5 < sz * 3) continue;  // < 60% assigned
        if (cnt == sz) continue;          // already fully assigned
        for (int i = 0; i < sz; i++) {
            int lit = c->literals[i];
            if (abs(lit) > max_var || abs(lit) == 0) continue;
            if (!active(lit)) continue;
            if (!val(lit))
                bump_variable_score(lit);
        }
    }
}

// Rebuild SEGA tracking data from scratch.  Called after preprocessing
// steps that may modify or substitute XOR clause literals (e.g., sweep,
// decompose, factor).  Iterates all non-garbage XOR clauses and rebuilds
// the counter / parity / var_to_long_xor mappings from current assignments.
void Internal::rebuild_sega_data()
{
    long_xor_clauses.clear ();
    xor_clause_counter.clear ();
    xor_clause_size.clear ();
    xor_clause_parity.clear ();
    var_to_long_xor.clear ();
    xor_full_clause.clear ();

    // Ensure var_to_long_xor has slots for all variables
    while ((int) var_to_long_xor.size () <= max_var)
      var_to_long_xor.push_back ({});

    for (auto c : xor_clauses) {
      if (c->garbage) continue;
      if (c->size <= 5) continue;  // short XOR handled by watches

      int idx = (int) long_xor_clauses.size ();
      long_xor_clauses.push_back (c);
      xor_clause_size.push_back (c->size);

      int cnt = 0;
      bool parity = false;
      for (int i = 0; i < c->size; i++) {
        int lit = c->literals[i];
        int v = abs (lit);

        while ((int) var_to_long_xor.size () <= v)
          var_to_long_xor.push_back ({});
        var_to_long_xor[v].push_back (idx);

        signed char vv = val (lit);
        if (vv) {
          cnt++;
          if (vv > 0) parity = !parity;
        }
      }
      xor_clause_counter.push_back (cnt);
      xor_clause_parity.push_back ((char) parity);

      if (cnt == c->size)
        xor_full_clause.push_back (idx);
    }
}

// Give initial score boosts to variables appearing in XOR clauses.
// This focuses the decision heuristic on XOR-constrained variables from
// the very beginning of search, rather than discovering them gradually.
void Internal::bump_xor_variable_scores()
{
    // Boost variables in all XOR clauses (both short and long)
    for (size_t i = 0; i < xor_clauses.size(); i++) {
        Clause *c = xor_clauses[i];
        if (c == nullptr || c->garbage) continue;
        for (int j = 0; j < c->size; j++) {
            int lit = c->literals[j];
            if (abs(lit) > max_var || abs(lit) == 0) continue;
            if (!active(lit)) continue;
            if (!val(lit))
                bump_variable_score(lit);
        }
    }
}

} // namespace CaDiCaL
