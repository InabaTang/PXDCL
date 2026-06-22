#include "internal.hpp"

namespace CaDiCaL {

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

// This function factors out clean up code common among the 'lucky'
// functions for backtracking and resetting a potential conflict.  One could
// also use exceptions here, but there are two different reasons for
// aborting early.  The first kind of aborting is due to asynchronous
// termination and the second kind due to a situation in which it is clear
// that a particular function will not be successful (for instance a
// completely negative clause is found).  The latter situation returns zero
// and will just abort the particular lucky function, while the former will
// abort all (by returning '-1').

int Internal::unlucky (int res) {
  if (level > 0)
    backtrack_without_updating_phases ();
  if (conflict)
    conflict = 0;
  return res;
}

int Internal::trivially_false_satisfiable () {
  LOG ("checking that all clauses contain a negative literal");
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    if (c->xor_flag) //TODO: xor_lucky
      continue;
    bool satisfied = false, found_negative_literal = false;
    if (c->xor_flag) printf("xor clause in lucky\n");
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      found_negative_literal = true;
      break;
    }
    if (satisfied || found_negative_literal)
      continue;
    LOG (c, "found purely positively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a negative literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky.constant.zero++;
  return 10;
}

int Internal::trivially_true_satisfiable () {
  LOG ("checking that all clauses contain a positive literal");
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    if (c->xor_flag) //TODO: xor_unlucky
      continue;
    bool satisfied = false, found_positive_literal = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      found_positive_literal = true;
      break;
    }
    if (satisfied || found_positive_literal)
      continue;
    LOG (c, "found purely negatively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a positive literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky.constant.one++;
  return 10;
}

/*------------------------------------------------------------------------*/
inline bool Internal::lucky_propagate_discrepency (int dec) {
  search_assume_decision (dec);
  bool no_conflict = propagate ();
  if (no_conflict)
    return false;
  if (level > 1) {
    conflict = nullptr;
    backtrack_without_updating_phases (level - 1);
    search_assume_decision (-dec);
    no_conflict = propagate ();
    if (no_conflict)
      return false;
    return true;
  } else {
    analyze ();
    assert (!level);
    no_conflict = propagate ();
    if (!no_conflict) {
      analyze ();
      LOG ("lucky inconsistency backward assigning to true");
      return true;
    }
  }
  return false;
}

int Internal::forward_false_satisfiable () {
  LOG ("checking increasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto idx : vars) {
  START:
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (-idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "forward assuming variables false satisfies formula");
  assert (satisfied ());
  stats.lucky.forward.zero++;
  return 10;
}

int Internal::forward_true_satisfiable () {
  LOG ("checking increasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto idx : vars) {
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "forward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.forward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::backward_false_satisfiable () {
  LOG ("checking decreasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (-idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "backward assuming variables false satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.zero++;
  return 10;
}

int Internal::backward_true_satisfiable () {
  LOG ("checking decreasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (auto it = vars.rbegin (); it != vars.rend (); ++it) {
    int idx = *it;
  START:
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    if (lucky_propagate_discrepency (idx)) {
      if (unsat)
        return 20;
      else
        return unlucky (0);
    } else
      goto START;
  }
  VERBOSE (1, "backward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

// The following two functions test if the formula is a satisfiable horn
// formula.  Actually the test is slightly more general.  It goes over all
// clauses and assigns the first positive literal to true and propagates.
// Already satisfied clauses are of course skipped.  A reverse function
// is not implemented yet.

int Internal::positive_horn_satisfiable () {
  LOG ("checking that all clauses are positive horn satisfiable");
  assert (!level);
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int positive_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      positive_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!positive_literal) {
      LOG (c, "no positive unassigned literal in");
      return unlucky (0);
    }
    assert (positive_literal > 0);
    LOG (c, "found positive literal %d in", positive_literal);
    search_assume_decision (positive_literal);
    if (propagate ())
      continue;
    LOG ("propagation of positive literal %d leads to conflict",
         positive_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", -idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are positive horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.positive++;
  return 10;
}

int Internal::lucky_decide_assumptions () {
  assert (!level);
  assert (!constraint.size ());
  int res = 0;
  while ((size_t) level < assumptions.size ()) {
    res = decide ();
    if (res == 20) {
      marked_failed = false;
      return 20;
    }
    if (!propagate ()) {
      break;
    }
  }

  if (conflict) {
    // analyze and learn from the conflict.
    LOG (conflict, "setting assumption lead to conflict");
    analyze_wrapper ();
    backtrack (0);
    assert (!conflict);
    int res = 0;
    while (!res) {
      assert ((size_t) level <= assumptions.size ());
      if (unsat)
        res = 20;
      else if (!propagate ()) {
        analyze_wrapper ();
      } else {
        res = decide_wrapper ();
      }
    }
    assert (res == 20);
    return 20;
  }
  return 0;
}

int Internal::negative_horn_satisfiable () {
  assert (!level);
  LOG ("checking that all clauses are negative horn satisfiable");
  int res = lucky_decide_assumptions ();
  if (res)
    return res;
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int negative_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      negative_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!negative_literal) {
      if (level > 0)
        backtrack_without_updating_phases ();
      LOG (c, "no negative unassigned literal in");
      return unlucky (0);
    }
    assert (negative_literal < 0);
    LOG (c, "found negative literal %d in", negative_literal);
    search_assume_decision (negative_literal);
    if (propagate ())
      continue;
    LOG ("propagation of negative literal %d leads to conflict",
         negative_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are negative horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.negative++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::lucky_phases () {
  assert (!level);
  require_mode (SEARCH);
  if (!opts.lucky)
    return 0;

  if (!opts.luckyassumptions && !assumptions.empty ())
    return 0;
  // TODO: Some of the lucky assignments can also be found if there are
  // constraint.
  // External propagator assumes a CDCL loop, so lucky is not tried here.
  if (!constraint.empty () || external_prop)
    return 0;
  if (!propagate ()) {
    learn_empty_clause ();
    return 20;
  }

  START (search);
  START (lucky);
  LOG ("starting lucky");
  assert (!searching_lucky_phases);
  searching_lucky_phases = true;
  stats.lucky.tried++;
  const int64_t active_before = stats.active;
  int res = trivially_false_satisfiable ();
  if (!res)
    res = trivially_true_satisfiable ();
  if (!res)
    res = forward_false_satisfiable ();
  if (!res)
    res = forward_true_satisfiable ();
  if (!res)
    res = backward_false_satisfiable ();
  if (!res)
    res = backward_true_satisfiable ();
  if (!res)
    res = negative_horn_satisfiable ();
  if (!res)
    res = positive_horn_satisfiable ();
  // XOR-aware strategy disabled: interacts poorly with SEGA during
  // lucky phases (!searching_lucky_phases guard blocks SEGA checks),
  // causing false positives on XOR satisfaction.
  // if (!res && !xor_clauses.empty ())
  //   res = xor_satisfiable ();
  if (res < 0)
    assert (termination_forced), res = 0;
  if (res == 10)
    stats.lucky.succeeded++;
  report ('l', !res);
  assert (searching_lucky_phases);

  assert (res || !level);
  if (res != 20) {
    if (!propagate ()) {
      LOG ("propagating units after elimination results in empty clause");
      learn_empty_clause ();
    }
  }

  const int64_t units = active_before - stats.active;

  if (!res && units)
    LOG ("lucky %" PRId64 " units", units);
  searching_lucky_phases = false;

  STOP (lucky);
  STOP (search);

  return res;
}

// XOR-aware lucky phase assignment: try assigning variables in XOR clauses
// to all-true or all-false, then check XOR satisfaction explicitly.
// SEGA is disabled during lucky phases (!searching_lucky_phases guard in
// propagate), so we manually check XOR clause satisfaction here.
int Internal::xor_satisfiable () {
  if (unsat) return 0;
  if (xor_clauses.empty ()) return 0;
  int res = lucky_decide_assumptions ();
  if (res) return res;

  // Strategy 1: try assigning all XOR-clause variables to true
  LOG ("checking XOR all-true phase assignment");
  for (auto c : xor_clauses) {
    if (terminated_asynchronously (10)) return unlucky (-1);
    if (c->garbage) continue;
    for (auto lit : *c) {
      int idx = abs (lit);
      if (val (idx)) continue;
      search_assume_decision (idx);     // assign positive
      if (!propagate ()) return unlucky (0);
    }
  }
  // Manually check XOR clause satisfaction (SEGA is disabled in lucky mode)
  if (propagated == trail.size ()) {
    bool all_xor_sat = true;
    for (auto c : xor_clauses) {
      if (c->garbage) continue;
      bool parity = false;
      for (auto lit : *c) {
        if (val (lit) > 0) parity = !parity;
      }
      if (!parity) { all_xor_sat = false; break; }
    }
    if (all_xor_sat && num_assigned == (size_t) max_var) {
      stats.lucky.succeeded++;
      return 10;
    }
  }
  backtrack ();

  // Strategy 2: try assigning all XOR-clause variables to false
  LOG ("checking XOR all-false phase assignment");
  for (auto c : xor_clauses) {
    if (terminated_asynchronously (10)) return unlucky (-1);
    if (c->garbage) continue;
    for (auto lit : *c) {
      int idx = abs (lit);
      if (val (idx)) continue;
      search_assume_decision (-idx);    // assign negative
      if (!propagate ()) return unlucky (0);
    }
  }
  if (propagated == trail.size ()) {
    bool all_xor_sat = true;
    for (auto c : xor_clauses) {
      if (c->garbage) continue;
      bool parity = false;
      for (auto lit : *c) {
        if (val (lit) > 0) parity = !parity;
      }
      if (!parity) { all_xor_sat = false; break; }
    }
    if (all_xor_sat && num_assigned == (size_t) max_var) {
      stats.lucky.succeeded++;
      return 10;
    }
  }

  return unlucky (0);
}

} // namespace CaDiCaL
