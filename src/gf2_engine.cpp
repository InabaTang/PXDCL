#include "gf2_engine.hpp"
#include "internal.hpp"
#include "format.hpp"

extern "C" {
#include <m4ri/m4ri.h>
}

namespace CaDiCaL {

GF2Engine::GF2Engine (Internal *i)
    : internal (i),
      xor_total_vars (0),
      last_assigned_count (0),
      calls (0), conflicts_found (0), implications_found (0),
      total_rows (0), total_cols (0),
      min_assigned_pct (15),     // start checking at 15% assigned
      min_new_assignments (40)   // re-check after 40+ new assignments
{}

GF2Engine::~GF2Engine () {}

void GF2Engine::rebuild () {
  xor_data.clear ();
  xor_total_vars = 0;
  last_assigned_count = 0;

  // Track which variables appear in XOR clauses
  std::vector<bool> seen (internal->max_var + 1, false);

  const auto &xc = internal->xor_clauses;
  for (size_t ci = 0; ci < xc.size (); ci++) {
    Clause *c = xc[ci];
    if (!c || c->garbage) continue;
    if (c->size < 2) continue;

    std::vector<int> lits;
    lits.reserve (c->size);
    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      lits.push_back (lit);
      int v = abs (lit);
      if (v > 0 && v <= internal->max_var && !seen[v]) {
        seen[v] = true;
        xor_total_vars++;
      }
    }
    xor_data.push_back (std::move (lits));
  }

  printf ("c GF2Engine: %zu clauses, %d XOR-active vars (%.1f%% of %d)\n",
          xor_data.size (), xor_total_vars,
          100.0 * xor_total_vars / internal->max_var, internal->max_var);
}

bool GF2Engine::should_check () {
  if (xor_data.empty ()) return false;

  // Count how many XOR-active variables are currently assigned
  int assigned = 0;
  for (int v = 1; v <= internal->max_var; v++) {
    if (internal->val (v)) {
      // Check if this variable is XOR-active by checking xor_occs
      if ((size_t) v < internal->xor_occs.size () &&
          internal->xor_occs[v] > 0)
        assigned++;
    }
  }

  // Trigger if: enough new assignments since last check, AND
  // enough total assigned to make GF(2) analysis worthwhile.
  // Reset tracking on backtrack/restart (when assigned count drops).
  if (assigned < last_assigned_count)
    last_assigned_count = 0;

  int new_since_last = assigned - last_assigned_count;
  int pct_assigned = xor_total_vars > 0 ?
                     (100 * assigned) / xor_total_vars : 0;

  if (new_since_last >= min_new_assignments &&
      pct_assigned >= min_assigned_pct) {
    last_assigned_count = assigned;
    return true;
  }

  return false;
}

mzd_t* GF2Engine::build_matrix (std::vector<int> &col_to_var) {
  if (xor_data.empty ()) return nullptr;

  int max_var = internal->max_var;

  // Build variable-to-column mapping for UNASSIGNED variables only
  std::vector<int> var_to_col;
  var_to_col.resize (max_var + 1, -1);
  col_to_var.clear ();

  for (const auto &lits : xor_data) {
    for (int lit : lits) {
      int v = abs (lit);
      if (v > 0 && v <= max_var && var_to_col[v] < 0 &&
          !internal->val (v) && internal->active (v)) {
        var_to_col[v] = (int) col_to_var.size ();
        col_to_var.push_back (v);
      }
    }
  }

  int ncols = (int) col_to_var.size () + 1;
  if (ncols <= 1 || ncols > 5000) return nullptr;

  int nrows = (int) xor_data.size ();
  if (nrows > 5000) return nullptr;

  mzd_t *mat = mzd_init (nrows, ncols);
  if (!mat) return nullptr;

  for (int row = 0; row < nrows; row++) {
    const auto &lits = xor_data[row];
    bool const_term = false;

    for (int lit : lits) {
      int v = abs (lit);
      if (v <= 0 || v > max_var) continue;

      int col = var_to_col[v];
      if (col >= 0) {
        mzd_write_bit (mat, row, col, 1);
      } else if (internal->val (v)) {
        bool val_true = (internal->val (v) > 0);
        if (lit < 0) val_true = !val_true;
        if (val_true) const_term = !const_term;
      }
    }

    // XOR constraint: l1^l2^...^lk = TRUE.
    // assigned_XOR ^ unassigned_XOR = TRUE
    // unassigned_XOR = TRUE ^ assigned_XOR = !const_term
    mzd_write_bit (mat, row, ncols - 1, const_term ? 0 : 1);
  }

  total_rows += nrows;
  total_cols += ncols;
  return mat;
}

int GF2Engine::scan_matrix (mzd_t *mat, const std::vector<int> &col_to_var,
                            std::vector<int> &implications) {
  int nrows = mat->nrows;
  int ncols = mat->ncols;
  int var_cols = ncols - 1;

  for (int r = 0; r < nrows; r++) {
    int var_bits = 0, last_var_col = -1;

    for (int c = 0; c < var_cols; c++) {
      if (mzd_read_bit (mat, r, c)) {
        var_bits++;
        last_var_col = c;
        if (var_bits > 1) break;
      }
    }

    bool const_bit = mzd_read_bit (mat, r, var_cols);

    if (var_bits == 0 && const_bit) {
      return r + 1;  // conflict: 0 = 1
    } else if (var_bits == 1 && last_var_col >= 0 &&
               (size_t) last_var_col < col_to_var.size ()) {
      int var = col_to_var[last_var_col];
      int implied_lit = const_bit ? var : -var;
      implications.push_back (implied_lit);
    }
  }

  return 0;
}

std::vector<int> GF2Engine::check () {
  calls++;
  std::vector<int> result;

  if (xor_data.empty ())
    return result;

  std::vector<int> col_to_var;
  mzd_t *mat = build_matrix (col_to_var);
  if (!mat)
    return result;

  mzd_echelonize (mat, true);

  std::vector<int> imps;
  int conflict_row = scan_matrix (mat, col_to_var, imps);

  mzd_free (mat);

  if (conflict_row > 0) {
    conflicts_found++;
    // GF(2) theory conflict detected but NOT used for backtracking.
    // Experiments show that GF(2)-generated conflict clauses produce
    // low-quality learned clauses that hurt CDCL performance (4x+ more
    // conflicts on r2).  The XOR watch mechanism already detects
    // conflicts efficiently through unit propagation — GF(2) conflicts
    // are redundant and generate worse learned clauses.
    //
    // We still log the conflict for diagnostic purposes, and CDCL
    // will find it naturally through SEGA or XOR watches.
    LOG ("GF2 engine: theory conflict at level %d (ignored)", internal->level);
    // Do NOT set result to -1 — let CDCL continue normally
  }

  // Found implications: each is a literal that MUST be assigned
  // for the XOR constraints to be satisfied.
  implications_found += imps.size ();
  result = std::move (imps);
  return result;
}

void GF2Engine::print_stats () {
  printf ("c GF2Engine: %" PRId64 " calls, %" PRId64 " implications, "
          "%" PRId64 " conflicts\n",
          calls, implications_found, conflicts_found);
  if (calls > 0)
    printf ("c GF2Engine: avg matrix %" PRId64 "x%" PRId64 ", "
            "%d total XOR vars\n",
            total_rows / calls, total_cols / calls, xor_total_vars);
}

} // namespace CaDiCaL
