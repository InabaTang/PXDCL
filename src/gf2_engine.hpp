#ifndef _gf2_engine_hpp_INCLUDED
#define _gf2_engine_hpp_INCLUDED

// GF(2) Theory Engine: CEGAR-style hybrid CDCL + GF(2) backend.
//
// Design:
//   1. XOR clause data is COPIED into a persistent, GC-safe structure
//      at preprocessing time.  The engine NEVER accesses `xor_clauses`
//      pointers during search.
//   2. The engine is triggered when CDCL has assigned enough XOR-active
//      variables to constrain the GF(2) subsystem.  This is NOT a fixed
//      interval — it's assignment-driven, like a proper CEGAR loop.
//   3. When enough assignments accumulate (default: 30% of XOR variables),
//      the engine builds an m4ri matrix, echelonizes it, and finds:
//      - Unit implications: rows with 1 variable bit → forced assignment
//      - Conflicts: rows with 0 variable bits + const=1 → UNSAT
//   4. Implications are returned to CDCL and DIRECTLY ASSIGNED via
//      search_assign_driving(), creating a positive feedback loop:
//      CDCL assigns variables → GF(2) finds implications → CDCL propagates
//      them → more GF(2) implications → ...
//   5. When the trail backtracks, assigned vars decrease, and the next
//      GF(2) call re-evaluates from the new (smaller) assignment.

#include <cstdint>
#include <vector>

struct mzd_t;

namespace CaDiCaL {

struct Internal;
struct Clause;

class GF2Engine {
private:
  Internal *internal;

  // Safe, persistent copy of XOR clause data.
  std::vector<std::vector<int>> xor_data;

  // Total XOR-active variables (computed at rebuild time)
  int xor_total_vars;

  // Assignment tracking: how many XOR vars were assigned at last check
  int last_assigned_count;

  // Statistics
  int64_t calls;
  int64_t conflicts_found;
  int64_t implications_found;
  int64_t total_rows;
  int64_t total_cols;

  // Configuration
  int min_assigned_pct;      // Minimum % of XOR vars assigned to trigger
  int min_new_assignments;    // Minimum new assignments since last check

  // Build an m4ri matrix from safe xor_data + current assignments.
  // Only includes columns for UNASSIGNED variables.
  mzd_t* build_matrix (std::vector<int> &col_to_var);

  // Scan the echelonized matrix for conflicts and implications.
  int scan_matrix (mzd_t *mat, const std::vector<int> &col_to_var,
                   std::vector<int> &implications);

public:
  GF2Engine (Internal *i);
  ~GF2Engine ();

  // Rebuild safe XOR clause data from solver's xor_clauses.
  void rebuild ();

  // Check if the engine should run given the current assignment state.
  // Returns true if enough XOR variables are assigned to warrant analysis.
  bool should_check ();

  // Run theory propagation.  Returns a vector of implied literals.
  // The caller MUST assign these via search_assign_driving(), using
  // the GF2 engine's theory reason clause as the reason.
  // Returns empty vector if no implications found, or {-1} on conflict.
  std::vector<int> check ();

  // Total XOR variables (for caller's assignment tracking)
  int total_vars () const { return xor_total_vars; }

  // Statistics
  void print_stats ();
};

} // namespace CaDiCaL

#endif
