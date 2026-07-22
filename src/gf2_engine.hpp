#ifndef _gf2_engine_hpp_INCLUDED
#define _gf2_engine_hpp_INCLUDED

// GF(2) Theory Engine: CEGAR-style Gaussian elimination over XOR constraints.
// Periodically called during CDCL search to detect theory conflicts and
// forced assignments that individual clause propagation misses.
//
// Architecture:
//   1. Collect unassigned XOR clauses from the solver
//   2. Build an m4ri dense matrix (rows = clauses, cols = unassigned vars + 1)
//   3. Substitute already-assigned variables (remove columns, adjust constants)
//   4. Run Gaussian elimination (mzd_echelonize)
//   5. Scan rows for conflicts (0=1) and implications (single remaining variable)
//   6. Return implications as unit clauses, conflicts as learned clauses

#include <cstdint>
#include <vector>

struct mzd_t;

namespace CaDiCaL {

struct Internal;
struct Clause;

class GF2Engine {
private:
  Internal *internal;

  // Statistics
  int64_t calls;          // Number of times theory propagation was called
  int64_t conflicts;      // Theory conflicts found
  int64_t implications;   // Theory implications found
  int64_t total_rows;     // Total rows in matrices built
  int64_t total_cols;     // Total columns in matrices built

  // Configuration
  int call_interval;      // Conflicts between theory propagation calls
  int min_unassigned;     // Minimum unassigned XOR vars to trigger analysis

  // Build an m4ri matrix from unassigned XOR clauses.
  // Maps unassigned variables to column indices.
  // Returns the matrix and column mapping.
  mzd_t* build_matrix (std::vector<int> &col_to_var);

  // Scan the echelonized matrix for conflicts and implications.
  // Returns: 0 = no conflict, >0 = conflict row index
  int scan_matrix (mzd_t *mat, const std::vector<int> &col_to_var,
                   std::vector<int> &implications);

  // Generate a conflict clause from a contradictory matrix row.
  void generate_conflict (mzd_t *mat, int conflict_row,
                          const std::vector<int> &col_to_var);

public:
  GF2Engine (Internal *i);
  ~GF2Engine ();

  // Run theory propagation: build matrix, eliminate, scan.
  // Returns: 0 = ok (possibly new implications added)
  //          -1 = theory conflict found (conflict clause set in solver)
  //          -2 = skipped (too few unassigned, or too frequent)
  int propagate ();

  // Get decision guidance: identify bottleneck variables from the
  // reduced XOR system.  Returns variables in priority order.
  std::vector<int> get_decision_candidates ();

  // Statistics
  void print_stats ();
};

} // namespace CaDiCaL

#endif
