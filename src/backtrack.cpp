#include "internal.hpp"

namespace CaDiCaL {

// The global assignment stack can only be (partially) reset through
// 'backtrack' which is the only function using 'unassign' (inlined and thus
// local to this file).  It turns out that 'unassign' does not need a
// specialization for 'probe' nor 'vivify' and thus it is shared.

inline void Internal::unassign (int lit) {
  assert (val (lit) > 0);
  set_val (lit, 0);

  int idx = vidx (lit);
  // Clear reason on unassign: prevents stale reason checks in
  // XOR/mixed circular reasoning guards after backtrack.
  // Without this, a literal assigned by an XOR clause at a low level
  // keeps its reason after backtrack, causing the guard to skip
  // re-checking when the clause becomes violated later.
  var (idx).reason = 0;
  LOG ("unassign %d @ %d", lit, var (idx).level);
  num_assigned--;

  // In the standard EVSIDS variable decision heuristic of MiniSAT, we need
  // to push variables which become unassigned back to the heap.
  //
  if (!scores.contains (idx))
    scores.push_back (idx);

  // For VMTF we need to update the 'queue.unassigned' pointer in case this
  // variable sits after the variable to which 'queue.unassigned' currently
  // points.  See our SAT'15 paper for more details on this aspect.
  //
  if (queue.bumped < btab[idx])
    update_queue_unassigned (idx);
}

/*------------------------------------------------------------------------*/

// Update the current target maximum assignment and also the very best
// assignment.  Whether a trail produces a conflict is determined during
// propagation.  Thus that all functions in the 'search' loop after
// propagation can assume that 'no_conflict_until' is valid.  If a conflict
// is found then the trail before the last decision is used (see the end of
// 'propagate').  During backtracking we can then save this largest
// propagation conflict free assignment.  It is saved as both 'target'
// assignment for picking decisions in 'stable' mode and if it is the
// largest ever such assignment also as 'best' assignment. This 'best'
// assignment can then be used in future stable decisions after the next
// 'rephase_best' overwrites saved phases with it.

void Internal::update_target_and_best () {

  if (opts.rephase == 2 && !stable)
    return;

  bool reset = (rephased && stats.conflicts > last.rephase.conflicts);

  if (reset) {
    target_assigned = 0;
    if (rephased == 'B')
      best_assigned = 0; // update it again
  }

  if (no_conflict_until > target_assigned) {
    copy_phases (phases.target);
    target_assigned = no_conflict_until;
    LOG ("new target trail level %zu", target_assigned);
  }

  if (no_conflict_until > best_assigned) {
    copy_phases (phases.best);
    best_assigned = no_conflict_until;
    LOG ("new best trail level %zu", best_assigned);
  }

  if (reset) {
    report (rephased);
    rephased = 0;
  }
}

/*------------------------------------------------------------------------*/

void Internal::backtrack (int new_level) {

  //printf("backtrack start\n");
  //printf("new_level = %d , level = %d\n",new_level,level);
  assert (new_level <= level);
  if (new_level == level)
    return;

  update_target_and_best ();
  backtrack_without_updating_phases (new_level);

  //printf("backtrack end\n");
}

void Internal::backtrack_without_updating_phases (int new_level) {

  assert (new_level <= level);
  if (new_level == level)
    return;

  // SEGA+MEGA: clearing on backtrack since counters changed
  xor_full_clause.clear();
  mixed_full_clauses.clear();

  stats.backtracks++;

  assert (num_assigned == trail.size ());

  const size_t assigned = control[new_level + 1].trail;

  LOG ("backtracking to decision level %d with decision %d and trail %zd",
       new_level, control[new_level].decision, assigned);

  const size_t end_of_trail = trail.size ();
  size_t i = assigned, j = i;

#ifdef LOGGING
  int unassigned = 0;
#endif
  int reassigned = 0;

  notify_backtrack (new_level);
  if (external_prop && !external_prop_is_lazy && !private_steps &&
      notified > assigned) {
    LOG ("external propagator is notified about some unassignments (trail: "
         "%zd, notified: %zd).",
         trail.size (), notified);
    notified = assigned;
  }

  while (i < end_of_trail) {
    int lit = trail[i++];
    Var &v = var (lit);
    if (v.level > new_level) {
      // SEGA: decrement counters + revert parity for long XOR clauses
      {
        int vv = abs(lit);
        if (vv < (int)var_to_long_xor.size()) {
          for (int ci : var_to_long_xor[vv]) {
            if (long_xor_clauses[ci] == nullptr) continue;
            xor_clause_parity[ci] = !xor_clause_parity[ci];
            xor_clause_counter[ci]--;
          }
        }
      }
      // Revert mixed clause parity and decrement MEGA counters
      {
        int vv = abs (lit);
        if (vv < (int) var_to_mixed.size ())
          for (auto &r : var_to_mixed[vv]) {
            if (mixed_clauses[r.ci] == nullptr) continue;
            if (r.clause_lit == lit)
              mixed_clauses[r.ci]->mixed_parity ^= (1ULL << r.bi);
            mixed_clause_counter[r.ci]--;
          }
      }
      unassign(lit);
#ifdef LOGGING
      unassigned++;
#endif
    } else {
      // This is the essence of the SAT'18 paper on chronological
      // backtracking.  It is possible to just keep out-of-order assigned
      // literals on the trail without breaking the solver (after some
      // modifications to 'analyze' - see 'opts.chrono' guarded code there).
      assert ((in_mode (BACKBONE)) || opts.chrono || external_prop ||
              did_external_prop);
#ifdef LOGGING
      if (!v.level)
        LOG ("reassign %d @ 0 unit clause %d", lit, lit);
      else
        LOG (v.reason, "reassign %d @ %d", lit, v.level);
#endif
      trail[j] = lit;
      v.trail = j++;
      reassigned++;
    }
  }
  trail.resize (j);
  LOG ("unassigned %d literals %.0f%%", unassigned,
       percent (unassigned, unassigned + reassigned));
  LOG ("reassigned %d literals %.0f%%", reassigned,
       percent (reassigned, unassigned + reassigned));

  if (propagated > assigned)
    propagated = assigned;
  if (propagated2 > assigned)
    propagated2 = assigned;
  if (no_conflict_until > assigned)
    no_conflict_until = assigned;

  propergated = 0; // Always go back to root-level.

  assert (notified <= assigned + reassigned);
  if (reassigned) {
    notify_assignments ();
  }

  control.resize (new_level + 1);
  level = new_level;
  if (changed_val) {
    assert (opts.ilb);
    if (!val (changed_val)) {
      changed_val = 0;
    }
  }

  if (opts.unionset)
  {
    _eqvRelationSize = _lv2EqvRelation[level];
    _xorUnion->BackJump(new_level);
  }

  // Plan A: Rebuild mixed clause watches that were lost during propagation
  if (!lost_mixed_watches.empty ()) {
    for (auto c : lost_mixed_watches) {
      // Safety: skip NULL or non-arena pointers (dangling after GC)
      if (!c) continue;
      if (!arena.contains ((char*)c)) {
        // Not in arena: check if in heap-allocated clauses
        bool found = false;
        for (auto &cl : clauses) if (cl == c) { found = true; break; }
        if (!found) continue;
      }
      if (c->garbage || !c->mixed_flag) continue;

      // Remove any existing watches from mixed_tab (they may be stale)
      for (int i = 0; i < c->size; i++) {
        int lit = c->literals[i];
        MixedWatches &mws = mixed_watches (lit);
        for (mixed_watch_iterator it = mws.begin (); it != mws.end ();) {
          if (it->clause == c)
            it = mws.erase(it);
          else
            ++it;
        }
      }

      // Find two literals to watch: prefer unassigned, then FALSE, then TRUE
      int w1 = -1, w2 = -1;
      // First pass: unassigned literals
      for (int i = 0; i < c->size; i++) {
        if (!val (c->literals[i])) {
          if (w1 < 0) w1 = i;
          else if (w2 < 0) { w2 = i; break; }
        }
      }
      // Second pass: FALSE literals
      if (w2 < 0) {
        for (int i = 0; i < c->size; i++) {
          if (i == w1) continue;
          if (val (c->literals[i]) < 0) {
            if (w1 < 0) w1 = i;
            else if (w2 < 0) { w2 = i; break; }
          }
        }
      }
      // Third pass: TRUE literals (clause is SAT, but we still need watches)
      if (w2 < 0) {
        for (int i = 0; i < c->size; i++) {
          if (i == w1) continue;
          if (val (c->literals[i]) > 0) {
            if (w1 < 0) w1 = i;
            else if (w2 < 0) { w2 = i; break; }
          }
        }
      }
      // Fallback: any two distinct positions
      if (w2 < 0 && w1 >= 0) {
        for (int i = 0; i < c->size; i++)
          if (i != w1) { w2 = i; break; }
      }
      if (w1 < 0) { w1 = 0; w2 = 1; } // absolute fallback

      if (w1 >= 0 && w2 >= 0 && w1 != w2) {
        c->mixed_w1 = w1;
        c->mixed_w2 = w2;
        const int l0 = c->literals[w1];
        const int l1 = c->literals[w2];
        watch_mixed_literal (l0, l1, c);
        watch_mixed_literal (l1, l0, c);
      }
    }
    lost_mixed_watches.clear ();
  }

  assert (num_assigned == trail.size ());
}

} // namespace CaDiCaL
