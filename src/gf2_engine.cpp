#include "gf2_engine.hpp"
#include "internal.hpp"
#include "format.hpp"
#include <algorithm>

extern "C" {
#include <m4ri/m4ri.h>
}

namespace CaDiCaL {

GF2Engine::GF2Engine (Internal *i)
    : internal (i),
      xor_total_vars (0),
      last_assigned_count (0),
      structural_inconsistent (false),
      synced_trail_size (0),
      calls (0), conflicts_found (0), implications_found (0),
      total_rows (0), total_cols (0), sparse_calls (0), dense_calls (0),
      sparse_conflicts (0), dense_conflicts (0),
      sparse_implications (0), dense_implications (0),
      min_assigned_pct (15),     // start checking at 15% assigned
      min_new_assignments (40),  // re-check after 40+ new assignments
      early_assigned_pct (70),   // early-trigger only at very high assignment ratio
      early_new_assignments (320), // and large assignment growth
      sparse_assigned_pct (72)
{}

GF2Engine::~GF2Engine () {}

void GF2Engine::rebuild () {
  xor_data.clear ();
  structural_basis.clear ();
  projected_rows.clear ();
  var_to_rows.clear ();
  trail_ops.clear ();
  xor_total_vars = 0;
  last_assigned_count = 0;
  structural_inconsistent = false;
  synced_trail_size = 0;

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
  rebuild_structural_basis ();
  rebuild_incremental_projection ();
}

bool GF2Engine::should_check_with_thresholds (int req_pct,
                                              int req_new_assignments) {
  if (xor_data.empty ()) return false;

  // O(1) tracked by search_assign/unassign.
  int assigned = internal->xor_assigned_count;

  // Trigger if: enough new assignments since last check, AND
  // enough total assigned to make GF(2) analysis worthwhile.
  // Reset tracking on backtrack/restart (when assigned count drops).
  if (assigned < last_assigned_count)
    last_assigned_count = 0;

  int new_since_last = assigned - last_assigned_count;
  int pct_assigned = xor_total_vars > 0 ?
                     (100 * assigned) / xor_total_vars : 0;

  if (new_since_last >= req_new_assignments &&
      pct_assigned >= req_pct) {
    last_assigned_count = assigned;
    return true;
  }

  return false;
}

bool GF2Engine::should_check () {
  return should_check_with_thresholds (min_assigned_pct,
                                       min_new_assignments);
}

bool GF2Engine::should_check_early () {
  // Keep early checks conservative to avoid frequent expensive matrix builds.
  return should_check_with_thresholds (early_assigned_pct,
                                       early_new_assignments);
}

bool GF2Engine::should_use_sparse_backend () const {
  if (xor_total_vars <= 0) return false;
  const int assigned = internal->xor_assigned_count;
  const int pct_assigned = (100 * assigned) / xor_total_vars;
  return pct_assigned >= sparse_assigned_pct;
}

void GF2Engine::xor_sorted_vectors (const std::vector<int> &a,
                                    const std::vector<int> &b,
                                    std::vector<int> &out) {
  out.clear ();
  out.reserve (a.size () + b.size ());
  size_t i = 0, j = 0;
  while (i < a.size () && j < b.size ()) {
    const int va = a[i], vb = b[j];
    if (va == vb) {
      i++;
      j++;
    } else if (va < vb) {
      out.push_back (va);
      i++;
    } else {
      out.push_back (vb);
      j++;
    }
  }
  while (i < a.size ()) out.push_back (a[i++]);
  while (j < b.size ()) out.push_back (b[j++]);
}

void GF2Engine::normalize_row_vars (std::vector<int> &vars) {
  if (vars.empty ()) return;
  std::sort (vars.begin (), vars.end ());
  std::vector<int> out;
  out.reserve (vars.size ());
  for (size_t i = 0; i < vars.size (); ) {
    size_t j = i + 1;
    while (j < vars.size () && vars[j] == vars[i]) j++;
    if (((j - i) & 1u) != 0u)
      out.push_back (vars[i]);
    i = j;
  }
  vars.swap (out);
}

int GF2Engine::recommended_interval (int implied,
                                     bool early_trigger) const {
  // Base interval used by original solver path.
  const int base = 4096;

  // If early trigger fired, do not accelerate checks; only back off on no gain.
  if (early_trigger) {
    if (implied == 0) return 8192;
    return base;
  }

  // Timed checks: keep base cadence when productive; back off when idle.
  if (implied == 0) return 8192;
  if (implied < 8) return 6144;
  return base;
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
    // Build equation over variable values x_v (not literal truth values):
    //   XOR_i literal_i = 1
    // where literal_i is either x_v (positive) or x_v ^ 1 (negative).
    // Every negative literal contributes a constant '+1' regardless of
    // whether its variable is assigned, so we have to account for that here.
    bool rhs = true;

    for (int lit : lits) {
      int v = abs (lit);
      if (v <= 0 || v > max_var) continue;

      if (lit < 0)
        rhs = !rhs;

      int col = var_to_col[v];
      if (col >= 0) {
        mzd_write_bit (mat, row, col, 1);
      } else if (internal->val (v)) {
        // Assigned variable contributes its variable value x_v to RHS.
        if (internal->val (v) > 0)
          rhs = !rhs;
      }
    }

    // unassigned_XOR(vars) = rhs
    mzd_write_bit (mat, row, ncols - 1, rhs ? 1 : 0);
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

void GF2Engine::rebuild_structural_basis () {
  structural_basis.clear ();
  structural_inconsistent = false;
  if (xor_data.empty ()) return;

  std::vector<int> pivot_to_row;
  pivot_to_row.resize (internal->max_var + 1, -1);
  std::vector<int> scratch;

  for (const auto &lits : xor_data) {
    SparseRow row;
    row.vars.clear ();
    row.vars.reserve (lits.size ());
    row.rhs = true;

    for (int lit : lits) {
      const int v = abs (lit);
      if (v <= 0 || v > internal->max_var) continue;
      row.vars.push_back (v);
      if (lit < 0)
        row.rhs = !row.rhs;
    }
    normalize_row_vars (row.vars);

    while (!row.vars.empty ()) {
      const int lead = row.vars[0];
      const int pivot_idx = (lead >= 0 && lead < (int) pivot_to_row.size ())
                                ? pivot_to_row[lead]
                                : -1;
      if (pivot_idx < 0)
        break;
      xor_sorted_vectors (row.vars, structural_basis[pivot_idx].vars, scratch);
      row.vars.swap (scratch);
      row.rhs ^= structural_basis[pivot_idx].rhs;
    }

    if (row.vars.empty ()) {
      if (row.rhs) {
        structural_inconsistent = true;
        return;
      }
      continue;
    }

    const int lead = row.vars[0];
    const int row_id = (int) structural_basis.size ();
    if (lead >= 0 && lead < (int) pivot_to_row.size ())
      pivot_to_row[lead] = row_id;
    structural_basis.push_back (std::move (row));
  }
}

void GF2Engine::rebuild_incremental_projection () {
  projected_rows.clear ();
  var_to_rows.clear ();
  trail_ops.clear ();
  synced_trail_size = 0;

  if (structural_basis.empty ())
    return;

  const int max_var = internal->max_var;
  if (max_var <= 0)
    return;

  projected_rows.reserve (structural_basis.size ());
  var_to_rows.resize (max_var + 1);

  for (const auto &src : structural_basis) {
    SparseRow row;
    row.rhs = src.rhs;
    row.vars.reserve (src.vars.size ());

    for (int v : src.vars) {
      if (v <= 0 || v > max_var)
        continue;
      if (internal->active (v)) {
        row.vars.push_back (v);
      } else {
        const signed char vv = internal->val (v);
        if (vv > 0)
          row.rhs = !row.rhs;
      }
    }

    const int row_id = (int) projected_rows.size ();
    projected_rows.push_back (std::move (row));
    for (int v : projected_rows[row_id].vars)
      var_to_rows[v].push_back (row_id);
  }
}

void GF2Engine::sync_projected_rows_to_trail () {
  const size_t trail_size = internal->trail.size ();

  // Roll back incremental projection on backtrack.
  while (synced_trail_size > trail_size && !trail_ops.empty ()) {
    const TrailOp &op = trail_ops.back ();
    for (int row_id : op.affected_rows) {
      if (row_id < 0 || row_id >= (int) projected_rows.size ())
        continue;
      SparseRow &row = projected_rows[row_id];
      auto it = std::lower_bound (row.vars.begin (), row.vars.end (), op.var);
      if (it == row.vars.end () || *it != op.var)
        row.vars.insert (it, op.var);
      if (op.value_true)
        row.rhs = !row.rhs;
    }
    trail_ops.pop_back ();
    synced_trail_size--;
  }

  // Apply new trail assignments incrementally.
  while (synced_trail_size < trail_size) {
    const int lit = internal->trail[synced_trail_size];
    const int var = abs (lit);
    const bool value_true = (lit > 0);

    TrailOp op;
    op.var = var;
    op.value_true = value_true;

    if (var > 0 && var < (int) var_to_rows.size ()) {
      const std::vector<int> &rows = var_to_rows[var];
      op.affected_rows.reserve (rows.size ());

      for (int row_id : rows) {
        if (row_id < 0 || row_id >= (int) projected_rows.size ())
          continue;
        SparseRow &row = projected_rows[row_id];
        auto it = std::lower_bound (row.vars.begin (), row.vars.end (), var);
        if (it != row.vars.end () && *it == var) {
          row.vars.erase (it);
          if (value_true)
            row.rhs = !row.rhs;
          op.affected_rows.push_back (row_id);
        }
      }
    }

    trail_ops.push_back (std::move (op));
    synced_trail_size++;
  }
}

int GF2Engine::check_sparse (std::vector<int> &implications) {
  // Assignment-projected sparse elimination on top of cached structural basis.
  if (structural_inconsistent)
    return 1;
  if (projected_rows.empty ())
    return 0;

  sync_projected_rows_to_trail ();

  const int max_var = internal->max_var;
  std::vector<SparseRow> basis;
  basis.reserve (projected_rows.size ());
  std::vector<int> pivot_to_row;
  pivot_to_row.resize (max_var + 1, -1);
  std::vector<int> scratch;
  std::vector<int> tmp;

  // Eliminate current projected rows into a sparse echelon basis.
  for (const auto &base : projected_rows) {
    SparseRow row;
    row.vars = base.vars;
    row.rhs = base.rhs;
    while (!row.vars.empty ()) {
      const int lead = row.vars[0];
      const int pivot_idx = (lead >= 0 && lead < (int) pivot_to_row.size ())
                                ? pivot_to_row[lead]
                                : -1;
      if (pivot_idx < 0)
        break;

      xor_sorted_vectors (row.vars, basis[pivot_idx].vars, scratch);
      row.vars.swap (scratch);
      row.rhs ^= basis[pivot_idx].rhs;
    }

    if (row.vars.empty ()) {
      if (row.rhs)
        return 1; // conflict: 0 = 1
      continue;
    }

    const int lead = row.vars[0];
    const int row_id = (int) basis.size ();
    if (lead >= 0 && lead < (int) pivot_to_row.size ())
      pivot_to_row[lead] = row_id;
    basis.push_back (std::move (row));
  }

  if (basis.empty ())
    return 0;

  // Reduce each pivot row at most once, in descending pivot order.
  std::vector<int> order;
  order.reserve (basis.size ());
  for (int pv = 1; pv <= max_var; pv++) {
    const int pidx = pivot_to_row[pv];
    if (pidx >= 0)
      order.push_back (pidx);
  }
  std::sort (order.begin (), order.end (),
             [&basis](int a, int b) {
               return basis[a].vars[0] > basis[b].vars[0];
             });

  std::vector<SparseRow> reduced (basis);
  std::vector<int> lead_to_reduced;
  lead_to_reduced.resize (max_var + 1, -1);

  for (int pidx : order) {
    SparseRow &row = reduced[pidx];
    bool changed = true;
    while (changed && row.vars.size () > 1) {
      changed = false;
      for (size_t k = 1; k < row.vars.size (); k++) {
        const int v = row.vars[k];
        const int ridx =
            (v >= 0 && v < (int) lead_to_reduced.size ()) ? lead_to_reduced[v] : -1;
        if (ridx < 0) continue;
        xor_sorted_vectors (row.vars, reduced[ridx].vars, tmp);
        row.vars.swap (tmp);
        row.rhs ^= reduced[ridx].rhs;
        changed = true;
        break;
      }
    }
    if (row.vars.empty ()) {
      if (row.rhs)
        return 1;
      continue;
    }
    lead_to_reduced[row.vars[0]] = pidx;
  }

  // Deduplicate unit implications and detect contradictory units early.
  std::vector<signed char> unit_sign;
  unit_sign.resize (max_var + 1, 0);
  for (int pidx : order) {
    const SparseRow &row = reduced[pidx];
    if (row.vars.size () != 1)
      continue;
    const int v = row.vars[0];
    const int lit = row.rhs ? v : -v;
    const signed char sign = (lit > 0) ? 1 : -1;
    if (v <= 0 || v > max_var)
      continue;
    if (!unit_sign[v]) {
      unit_sign[v] = sign;
      const signed char vv = internal->val (v);
      if (!vv)
        implications.push_back (lit);
      else if ((vv > 0 && sign < 0) || (vv < 0 && sign > 0))
        return 1;
    } else if (unit_sign[v] != sign) {
      return 1;
    }
  }

  return 0;
}

std::vector<int> GF2Engine::check () {
  calls++;
  std::vector<int> result;

  if (xor_data.empty ())
    return result;

  std::vector<int> imps;
  int conflict_row = 0;
  const bool use_sparse = should_use_sparse_backend ();

  if (use_sparse) {
    sparse_calls++;
    conflict_row = check_sparse (imps);
  } else {
    dense_calls++;
    std::vector<int> col_to_var;
    mzd_t *mat = build_matrix (col_to_var);
    if (!mat)
      return result;

    mzd_echelonize (mat, true);
    conflict_row = scan_matrix (mat, col_to_var, imps);
    mzd_free (mat);
  }

  if (conflict_row > 0) {
    conflicts_found++;
    if (use_sparse)
      sparse_conflicts++;
    else
      dense_conflicts++;
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
  if (use_sparse)
    sparse_implications += imps.size ();
  else
    dense_implications += imps.size ();

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
  printf ("c GF2Engine: sparse=%" PRId64 " calls (%" PRId64
          " imps, %" PRId64 " conflicts), dense=%" PRId64
          " calls (%" PRId64 " imps, %" PRId64 " conflicts)\n",
          sparse_calls, sparse_implications, sparse_conflicts,
          dense_calls, dense_implications, dense_conflicts);
}

} // namespace CaDiCaL
