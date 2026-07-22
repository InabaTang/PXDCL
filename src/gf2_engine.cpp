#include "gf2_engine.hpp"
#include "internal.hpp"
#include "format.hpp"

extern "C" {
#include <m4ri/m4ri.h>
}

namespace CaDiCaL {

GF2Engine::GF2Engine (Internal *i)
    : internal (i),
      calls (0), conflicts (0), implications (0),
      total_rows (0), total_cols (0),
      call_interval (1000),
      min_unassigned (50)
{}

GF2Engine::~GF2Engine () {}

mzd_t* GF2Engine::build_matrix (std::vector<int> &col_to_var) {
  int max_var = internal->max_var;

  // Collect unassigned variables from SEGA-tracked long XOR clauses
  // (safe: SEGA indices are validated on every access)
  std::vector<int> var_to_col;
  var_to_col.resize (max_var + 1, -1);
  col_to_var.clear ();

  const auto &lx = internal->long_xor_clauses;
  for (size_t ci = 0; ci < lx.size (); ci++) {
    Clause *c = lx[ci];
    if (!c || c->garbage) continue;
    if (ci >= internal->xor_clause_size.size ()) continue;
    if (c->size != internal->xor_clause_size[ci]) continue;
    for (int i = 0; i < c->size; i++) {
      int v = abs (c->literals[i]);
      if (v > 0 && v <= max_var && var_to_col[v] < 0 &&
          !internal->val (v) && internal->active (v)) {
        var_to_col[v] = (int) col_to_var.size ();
        col_to_var.push_back (v);
      }
    }
  }

  int ncols = (int) col_to_var.size () + 1;
  if (ncols <= 1 || ncols > 2000) return nullptr;  // safety limit

  int nrows = 0;
  for (size_t ci = 0; ci < lx.size (); ci++) {
    Clause *c = lx[ci];
    if (!c || c->garbage) continue;
    if (ci >= internal->xor_clause_size.size ()) continue;
    if (c->size != internal->xor_clause_size[ci]) continue;
    nrows++;
  }

  if (nrows <= 0 || nrows > 2000) return nullptr;  // safety limit

  mzd_t *mat = mzd_init (nrows, ncols);
  if (!mat) return nullptr;

  int row = 0;
  for (size_t ci = 0; ci < lx.size (); ci++) {
    Clause *c = lx[ci];
    if (!c || c->garbage) continue;
    if (ci >= internal->xor_clause_size.size ()) continue;
    if (c->size != internal->xor_clause_size[ci]) continue;

    bool const_term = false;
    for (int i = 0; i < c->size; i++) {
      int lit = c->literals[i];
      int v = abs (lit);
      if (v <= 0 || v > max_var) continue;

      int col = var_to_col[v];
      if (col >= 0) {
        mzd_write_bit (mat, row, col, 1);
      } else if (v <= max_var && internal->val (v)) {
        bool val_true = (internal->val (v) > 0);
        if (lit < 0) val_true = !val_true;
        if (val_true) const_term = !const_term;
      }
    }
    mzd_write_bit (mat, row, ncols - 1, const_term ? 1 : 0);
    row++;
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
      }
    }

    bool const_bit = mzd_read_bit (mat, r, var_cols);

    if (var_bits == 0 && const_bit) {
      return r + 1;  // conflict
    } else if (var_bits == 1 && last_var_col >= 0 &&
               (size_t)last_var_col < col_to_var.size()) {
      int var = col_to_var[last_var_col];
      int implied_lit = const_bit ? var : -var;
      implications.push_back (implied_lit);
    }
  }

  return 0;
}

void GF2Engine::generate_conflict (mzd_t *, int,
                                    const std::vector<int> &) {
  // Not used during search — conflicts are handled by SEGA
}

int GF2Engine::propagate () {
  calls++;

  // Count active long XOR clauses
  int active_xor = 0;
  for (size_t ci = 0; ci < internal->long_xor_clauses.size (); ci++) {
    Clause *c = internal->long_xor_clauses[ci];
    if (c && !c->garbage) active_xor++;
  }
  if (active_xor < 10 || active_xor > 5000) return 0;

  // Count unassigned XOR-active variables
  int unassigned_xor_vars = 0;
  for (int v = 1; v <= internal->max_var; v++) {
    if (!internal->active (v)) continue;
    if (internal->val (v)) continue;
    if ((size_t)v < internal->xor_occs.size () && internal->xor_occs[v] > 0)
      unassigned_xor_vars++;
  }
  if (unassigned_xor_vars < min_unassigned) return 0;
  // Performance guard: skip if matrix would be too large
  if (active_xor * unassigned_xor_vars > 2000000) return 0;

  std::vector<int> col_to_var;
  mzd_t *mat = build_matrix (col_to_var);
  if (!mat) return 0;

  mzd_echelonize (mat, true);

  std::vector<int> imps;
  int conflict_row = scan_matrix (mat, col_to_var, imps);

  mzd_free (mat);

  if (conflict_row > 0) {
    conflicts++;
    return -1;
  }

  // Bump VSIDS scores for theory-implied variables (decision guidance)
  for (int lit : imps) {
    implications++;
    int v = abs (lit);
    if (v > 0 && v <= internal->max_var &&
        !internal->val (v) && internal->active (v)) {
      if (internal->use_scores ()) {
        internal->bump_variable_score (v);
        internal->bump_variable_score (v);  // double bump for implied vars
      }
    }
  }

  return (int) imps.size ();
}

std::vector<int> GF2Engine::get_decision_candidates () {
  std::vector<int> candidates;
  std::vector<std::pair<int,int>> sorted;
  for (int v = 1; v <= internal->max_var; v++) {
    if (!internal->active (v)) continue;
    if (internal->val (v)) continue;
    if ((size_t)v < internal->xor_occs.size ()) {
      int occs = internal->xor_occs[v];
      if (occs > 0) sorted.push_back ({-occs, v});
    }
  }
  std::sort (sorted.begin (), sorted.end ());
  for (size_t i = 0; i < sorted.size () && i < 10; i++)
    candidates.push_back (sorted[i].second);
  return candidates;
}

void GF2Engine::print_stats () {
  printf ("c GF2Engine: %" PRId64 " calls, %" PRId64 " conflicts, "
          "%" PRId64 " implications\n",
          calls, conflicts, implications);
  if (calls > 0)
    printf ("c GF2Engine: avg matrix %" PRId64 "x%" PRId64 "\n",
            total_rows / calls, total_cols / calls);
}

} // namespace CaDiCaL
