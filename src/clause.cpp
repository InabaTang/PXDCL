#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Signed marking or unmarking of a clause or the global 'clause'.

void Internal::mark (Clause *c) {
  for (const auto &lit : *c)
    mark (lit);
}

void Internal::mark2 (Clause *c) {
  for (const auto &lit : *c)
    mark2 (lit);
}

void Internal::unmark (Clause *c) {
  for (const auto &lit : *c)
    unmark (lit);
}

void Internal::mark_clause () {
  for (const auto &lit : clause)
    mark (lit);
}

void Internal::unmark_clause () {
  for (const auto &lit : clause)
    unmark (lit);
}

/*------------------------------------------------------------------------*/

// Mark the variables of an irredundant clause to 'have been removed', which
// will trigger these variables to be considered again in the next bounded
// variable elimination phase.  This is called from 'mark_garbage' below.
// Note that 'mark_removed (int lit)' will also mark the blocking flag of
// '-lit' to trigger reconsidering blocking clauses on '-lit'.

void Internal::mark_removed (Clause *c, int except) {
  LOG (c, "marking removed");
  assert (!c->redundant);
  for (const auto &lit : *c)
    if (lit != except)
      mark_removed (lit);
}

// Mark the variables of a (redundant or irredundant) clause to 'have been
// added', which triggers clauses with such a variables, to be considered
// both as a subsumed or subsuming clause in the next subsumption phase.
// This function is called from 'new_clause' below as well as in situations
// where a clause is shrunken (and thus needs to be at least considered
// again to subsume a larger clause).  We also use this to tell
// 'ternary' preprocessing reconsider clauses on an added literal as well as
// trying to block clauses on it.

inline void Internal::mark_added (int lit, int size, bool redundant) {
  mark_subsume (lit);
  if (size == 3)
    mark_ternary (lit);
  if (!redundant)
    mark_block (lit);
  if ((!redundant || size == 2))
    mark_factor (lit);
}

void Internal::mark_added (Clause *c) {
  LOG (c, "marking added");
  assert (likely_to_be_kept_clause (c));
  for (const auto &lit : *c)
    mark_added (lit, c->size, c->redundant);
}

/*------------------------------------------------------------------------*/

Clause *Internal::new_clause (bool red, int glue) {

  assert (clause.size () <= (size_t) INT_MAX);
  const int size = (int) clause.size ();
  assert (size >= 2);

  if (glue > size)
    glue = size;

  // Determine number of blocks for mixed clauses
  int num_blocks = mixed_clause_flag ? (int) mixed_block_offsets.size () : 0;
  size_t bytes = Clause::bytes (size, num_blocks);
  Clause *c = (Clause *) new char[bytes];
  DeferDeleteArray<char> clause_delete ((char *) c);

  c->id = ++clause_id;

  c->conditioned = false;
  c->covered = false;
  c->enqueued = false;
  c->frozen = false;
  c->garbage = false;
  c->gate = false;
  c->hyper = false;
  c->instantiated = false;
  c->moved = false;
  c->reason = false;
  c->redundant = red;
  c->transred = false;
  c->subsume = false;
  c->swept = false;
  c->flushed = false;
  c->vivified = false;
  c->vivify = false;
  c->used = 0;

  // Initialize mixed clause fields
  // Single-block mixed clauses → convert to pure XOR immediately
  if (mixed_clause_flag && num_blocks <= 1) {
    c->mixed_flag = 0;
    c->xor_flag = true;
  } else if (mixed_clause_flag && num_blocks > 0
             && (size_t) num_blocks <= mixed_block_offsets.size ()
             && num_blocks <= size) {
    c->xor_flag = false;
    c->mixed_flag = 1;
    c->mixed_w1 = 0;
    c->mixed_w2 = 1;
    c->mixed_num_blocks = num_blocks;
    c->mixed_parity = 0;
  } else {
    c->mixed_flag = 0;
    if (xor_clause_flag) c->xor_flag = true;
    else c->xor_flag = false;
  }

  c->xor_conflict_flag = false;

  c->glue = glue;
  c->size = size;
  c->pos = 2;

  for (int i = 0; i < size; i++)
  {
    //if (c->xor_flag) printf("%d : %d \n",i,clause[i]);
    c->literals[i] = clause[i];
  }

  // Copy block offsets AFTER literals and AFTER c->size is set
  if (c->mixed_flag && num_blocks > 0) {
    int *offsets = c->block_offsets ();
    for (int i = 0; i < num_blocks; i++)
      offsets[i] = mixed_block_offsets[i];
  }

  // Just checking that we did not mess up our sophisticated memory layout.
  // This might be compiler dependent though. Crucial for correctness.
  //
  assert (c->bytes () == bytes);

  stats.current.total++;
  stats.added.total++;

  if (red) {
    stats.current.redundant++;
    stats.added.redundant++;
  } else {
    stats.irrlits += size;
    stats.current.irredundant++;
    stats.added.irredundant++;
  }

  clauses.push_back (c);

  // Convert single-block mixed to pure XOR
  if (c->mixed_flag && num_blocks <= 1) {
    c->mixed_flag = 0;
    c->xor_flag = 1;
    xor_clauses.push_back (c);
  } else if (c->mixed_flag) {
    mixed_clauses.push_back (c);
  } else if (xor_clause_flag) {
    xor_clauses.push_back(c);
    // Register long XOR clauses for SEGA lazy evaluation
    if (c->size > 5) {
      int idx = (int)long_xor_clauses.size();
      long_xor_clauses.push_back(c);
      xor_clause_counter.push_back(0);
      xor_clause_size.push_back(c->size);
      xor_clause_parity.push_back(false);
      // Ensure var_to_long_xor is large enough
      for (int i = 0; i < c->size; i++) {
        int lit = c->literals[i];
        int v = abs(lit);
        while ((int)var_to_long_xor.size() <= v)
          var_to_long_xor.push_back({});
        var_to_long_xor[v].push_back(idx);
      }
    }
  }
  clause_delete.release ();
  LOG (c, "new pointer %p", (void *) c);

  if (likely_to_be_kept_clause (c))
    mark_added (c);

  return c;
}

/*------------------------------------------------------------------------*/

void Internal::promote_clause (Clause *c, int new_glue) {
  assert (c->redundant);
  assert (new_glue);
  const int tier1limit = tier1[false];
  const int tier2limit = max (tier1limit, tier2[false]);
  if (!c->redundant)
    return;
  if (c->hyper)
    return;
  int old_glue = c->glue;
  if (new_glue >= old_glue)
    return;
  c->used = max_used;
  if (old_glue > tier1limit && new_glue <= tier1limit) {
    LOG (c, "promoting with new glue %d to tier1", new_glue);
    stats.promoted1++;
  } else if (old_glue > tier2limit && new_glue <= tier2limit) {
    LOG (c, "promoting with new glue %d to tier2", new_glue);
    stats.promoted2++;
  } else if (old_glue <= tier2limit)
    LOG (c, "keeping with new glue %d in tier2", new_glue);
  else
    LOG (c, "keeping with new glue %d in tier3", new_glue);
  stats.improvedglue++;
  c->glue = new_glue;
}
/*------------------------------------------------------------------------*/

void Internal::promote_clause_glue_only (Clause *c, int new_glue) {
  assert (c->redundant);
  assert (new_glue);
  if (c->hyper)
    return;
  int old_glue = c->glue;
  const int tier1limit = tier1[false];
  const int tier2limit = max (tier1limit, tier2[false]);
  if (new_glue >= old_glue)
    return;
  if (new_glue <= tier1limit) {
    LOG (c, "promoting with new glue %d to tier1", new_glue);
    stats.promoted1++;
  } else if (old_glue > tier2limit && new_glue <= tier2limit) {
    LOG (c, "promoting with new glue %d to tier2", new_glue);
    stats.promoted2++;
  } else if (old_glue <= tier2limit)
    LOG (c, "keeping with new glue %d in tier2", new_glue);
  else
    LOG (c, "keeping with new glue %d in tier3", new_glue);
  stats.improvedglue++;
  c->glue = new_glue;
}

/*------------------------------------------------------------------------*/

// Shrinking a clause, e.g., removing one or more literals, requires to fix
// the 'pos' field, if it exists and points after the new last literal. We
// also have adjust the global statistics counter of irredundant literals
// for irredundant clauses, and also adjust the glue value of redundant
// clauses if the size becomes smaller than the glue.  Also mark the
// literals in the resulting clause as 'added'.  The result is the number of
// (aligned) removed bytes, resulting from shrinking the clause.
//
size_t Internal::shrink_clause (Clause *c, int new_size) {
  if (opts.check && is_external_forgettable (c->id))
    mark_garbage_external_forgettable (c->id);
  assert (new_size >= 2);
  int old_size = c->size;
  assert (new_size < old_size);
#ifndef NDEBUG
  for (int i = c->size; i < new_size; i++)
    c->literals[i] = 0;
#endif

  if (c->pos >= new_size)
    c->pos = 2;

  size_t old_bytes = c->bytes ();
  c->size = new_size;
  size_t new_bytes = c->bytes ();
  size_t res = old_bytes - new_bytes;

  if (c->redundant)
    promote_clause_glue_only (c, min (c->size - 1, c->glue));
  else {
    int delta_size = old_size - new_size;
    assert (stats.irrlits >= delta_size);
    stats.irrlits -= delta_size;
  }

  if (likely_to_be_kept_clause (c))
    mark_added (c);

  return res;
}

// This is the 'raw' deallocation of a clause.  If the clause is in the
// arena nothing happens.  If the clause is not in the arena its memory is
// reclaimed immediately.

void Internal::deallocate_clause (Clause *c) {
  char *p = (char *) c;
  if (arena.contains (p))
    return;
  LOG (c, "deallocate pointer %p", (void *) c);
  delete[] p;
}

void Internal::delete_clause (Clause *c) {
  LOG (c, "delete pointer %p", (void *) c);

  // SEGA: null out any reference to this clause in long_xor_clauses
  // before deallocation prevents dangling pointers in hot paths.
  if (c->xor_flag && c->size > 5) {
    for (size_t ci = 0; ci < long_xor_clauses.size (); ci++) {
      if (long_xor_clauses[ci] == c)
        long_xor_clauses[ci] = nullptr;
    }
  }

  size_t bytes = c->bytes ();
  stats.collected += bytes;
  if (c->garbage) {
    assert (stats.garbage.bytes >= (int64_t) bytes);
    stats.garbage.bytes -= bytes;
    assert (stats.garbage.clauses > 0);
    stats.garbage.clauses--;
    assert (stats.garbage.literals >= c->size);
    stats.garbage.literals -= c->size;

    // See the discussion in 'propagate' on avoiding to eagerly trace binary
    // clauses as deleted (produce 'd ...' lines) as soon they are marked
    // garbage.  We avoid this and only trace them as deleted when they are
    // actually deleted here.  This allows the solver to propagate binary
    // garbage clauses without producing incorrect 'd' lines.  The effect
    // from the proof perspective is that the deletion of these binary
    // clauses occurs later in the proof file.
    //
    if (proof && c->size == 2 && !c->flushed) {
      proof->delete_clause (c);
    }
  }
  deallocate_clause (c);
}

// We want to eagerly update statistics as soon clauses are marked garbage.
// Otherwise 'report' for instance gives wrong numbers after 'subsume'
// before the next 'reduce'.  Thus we factored out marking and accounting
// for garbage clauses.
//
// Eagerly deleting clauses instead is problematic, since references to
// these clauses need to be flushed, which is too costly to do eagerly.
//
// We also update garbage statistics at this point.  This helps to
// determine whether the garbage collector should be called during for
// instance bounded variable elimination, which usually generates lots of
// garbage clauses.
//
// In order not to miss any update to these clause statistics we call
// 'check_clause_stats' after garbage collection in debugging mode.
//
void Internal::mark_garbage (Clause *c) {

  assert (!c->garbage);
  //if (c->xor_flag) printf("mark garbage xor clause \n");

  // Delay tracing deletion of binary clauses.  See the discussion above in
  // 'delete_clause' and also in 'propagate'.
  //
  if (proof && (c->size != 2 || !watching ())) {
    c->flushed = true;
    proof->delete_clause (c);
  }

  // Because of the internal model checking, external forgettable clauses
  // must be marked as removed already upon mark_garbage, can not wait until
  // actual deletion.
  if (opts.check && is_external_forgettable (c->id))
    mark_garbage_external_forgettable (c->id);

  assert (stats.current.total > 0);
  stats.current.total--;

  size_t bytes = c->bytes ();
  if (c->redundant) {
    assert (stats.current.redundant > 0);
    stats.current.redundant--;
  } else {
    assert (stats.current.irredundant > 0);
    stats.current.irredundant--;
    assert (stats.irrlits >= c->size);
    stats.irrlits -= c->size;
    mark_removed (c);
  }
  stats.garbage.bytes += bytes;
  stats.garbage.clauses++;
  stats.garbage.literals += c->size;
  c->garbage = true;
  c->used = 0;

  LOG (c, "marked garbage pointer %p", (void *) c);
}

/*------------------------------------------------------------------------*/

// Almost the same function as 'search_assign' except that we do not pretend
// to learn a new unit clause (which was confusing in log files).

void Internal::assign_original_unit (int64_t id, int lit) { //Find : ori_unit
  assert (!level || opts.chrono);
  assert (!unsat);
  const int idx = vidx (lit);
  assert (!vals[idx]);
  assert (!flags (idx).eliminated ());
  Var &v = var (idx);
  v.level = 0;
  v.trail = (int) trail.size ();
  v.reason = 0;
  const signed char tmp = sign (lit);
  set_val (idx, tmp);
  trail.push_back (lit);
  num_assigned++;
  const unsigned uidx = vlit (lit);
  if (lrat || frat)
    unit_clauses (uidx) = id;
  LOG ("original unit assign %d", lit);
  // DISABLED
  { int v = abs (lit);
    if (v < (int) var_to_mixed.size ())
      for (auto &r : var_to_mixed[v])
        if (r.clause_lit == lit)
          mixed_clauses[r.ci]->mixed_parity ^= (1ULL << r.bi); }
  assert (num_assigned == trail.size () || level);
  mark_fixed (lit);
  if (level)
    return;
  if (propagate ())
    return;
  assert (conflict);
  LOG ("propagation of original unit results in conflict");
  learn_empty_clause ();
}

// New clause added through the API, e.g., while parsing a DIMACS file.
// Also used by external_propagate in various different modes.
// clause, original, lrat_chain and external->eclause are set.
// from_propagator and force_no_backtrack change the behaviour.
// sometimes the pointer to the new clause is needed, therefore it is
// made sure that newest_clause points to the new clause upon return.

void Internal::add_new_original_clause (int64_t id) {
  // Save and immediately reset flags to prevent state leaks
  // in early-return / skip paths (e.g., tautology, unsatisfiable).
  bool is_xor = xor_clause_flag;
  bool is_mixed = mixed_clause_flag;
  // Save and clear block offsets for mixed clauses
  vector<int> saved_mixed_block_offsets;
  if (is_mixed)
    saved_mixed_block_offsets.swap (mixed_block_offsets);
  xor_clause_flag = false;
  mixed_clause_flag = false;

  //if (xor_clause_flag) printf("add new original clause : %ld\n",id);
  if (!from_propagator && level && !opts.ilb) {
    backtrack ();
  } else if (changed_val) {
    assert (val (changed_val));
    int new_level = var (changed_val).level - 1;
    assert (new_level >= 0);
    backtrack (new_level);
  }
  assert (!changed_val);
  LOG (original, "original clause");
  assert (clause.empty ());
  bool skip = false;
  unordered_set<int> learned_levels;
  size_t unassigned = 0;
  newest_clause = 0;
  if (unsat) {
    LOG ("skipping clause since formula is already inconsistent");
    skip = true;
  } else {
    assert (clause.empty ());
    if (is_mixed) {
      // For mixed clauses, push all literals directly (no dedup or remove)
      // Block structure is preserved via mixed_block_offsets
      for (const auto &lit : original) {
        clause.push_back (lit);
      }
    } else if (!is_xor) {
      for (const auto &lit : original) {
        int tmp = marked (lit);
        if (tmp > 0) {
          LOG ("removing duplicated literal %d", lit);
        } else if (tmp < 0) {
          LOG ("tautological since both %d and %d occur", -lit, lit);
          skip = true;
        } else {
          mark (lit);
          tmp = fixed (lit);
          if (tmp < 0) {
            LOG ("removing falsified literal %d", lit);
            if (lrat) {
              int elit = externalize (lit);
              unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
              if (!external->ext_units[eidx]) {
                int64_t uid = unit_id (-lit);
                lrat_chain.push_back (uid);
              }
            }
          } else if (tmp > 0) {
            LOG ("satisfied since literal %d true", lit);
            skip = true;
          } else {
            clause.push_back (lit);
            assert (flags (lit).status != Flags::UNUSED);
            tmp = val (lit);
            if (tmp)
              learned_levels.insert (var (lit).level);
            else
              unassigned++;
          }
        }
      }
      for (const auto &lit : original)
        unmark (lit);
    }
    else
    {
      for (const auto &lit : original) {
        clause.push_back(lit);
        int tmp = fixed(lit);
        if (tmp < 0) {
          LOG("falsified literal %d in XOR clause", lit);
          if (lrat) {
            int elit = externalize(lit);
            unsigned eidx = (elit > 0) + 2u * (unsigned) abs(elit);
            if (!external->ext_units[eidx]) {
              int64_t uid = unit_id(-lit);
              lrat_chain.push_back(uid);
            }
          }
        } else if (tmp > 0) {
          LOG("satisfied literal %d in XOR clause", lit);
        } else {
          tmp = val(lit);
          if (tmp)
            learned_levels.insert(var(lit).level);
          else
            unassigned++;
        }
      }
    }
  }

  // if (xor_clause_flag)
  // {
  //   for (auto it : clause)
  //   {
  //     printf("%d ",it);
  //   }
  //   printf("\n");
  // }
  if (skip) {
    if (from_propagator) {
      stats.ext_prop.elearn_conf++;

      // In case it was a skipped external forgettable, we need to mark it
      // immediately as removed

      if (opts.check && is_external_forgettable (id))
        mark_garbage_external_forgettable (id);
    }
    if (proof) {
      proof->delete_external_original_clause (id, false, external->eclause);
    }
  } else {
    int64_t new_id = id;
    const size_t size = clause.size ();
    if (original.size () > size) {
      new_id = ++clause_id;
      if (proof) {
        if (lrat)
          lrat_chain.push_back (id);
        proof->add_derived_clause (new_id, false, clause, lrat_chain);
        proof->delete_external_original_clause (id, false,
                                                external->eclause);
      }
      external->check_learned_clause ();

      if (from_propagator) {
        // The original form of the added clause is immediately forgotten
        // TODO: shall we save and check the simplified form? (one with
        // new_id)
        if (opts.check && is_external_forgettable (id))
          mark_garbage_external_forgettable (id);
      }
    }

    external->eclause.clear ();
    lrat_chain.clear ();

    if (!size) {
      if (from_propagator)
        stats.ext_prop.elearn_conf++;
      assert (!unsat);
      if (!original.size ())
        VERBOSE (1, "found empty original clause");
      else
        VERBOSE (1, "found falsified original clause");
      unsat = true;
      conflict_id = new_id;
      marked_failed = true;
      conclusion.push_back (new_id);
    } else if (size == 1) {
      if (force_no_backtrack) {
        assert (level);
        const int idx = vidx (clause[0]);
        assert (val (clause[0]) >= 0);
        assert (!flags (idx).eliminated ());
        Var &v = var (idx);
        assert (val (clause[0]));
        v.level = 0;
        v.reason = 0;
        did_external_prop = true;
        const unsigned uidx = vlit (clause[0]);
        if (lrat || frat)
          unit_clauses (uidx) = new_id;
        mark_fixed (clause[0]);
      } else {
        const int lit = clause[0];
        assert (!val (lit) || var (lit).level);
        if (val (lit) < 0)
          backtrack (var (lit).level - 1);
        assert (val (lit) >= 0);
        handle_external_clause (0);
        assign_original_unit (new_id, lit);
      }
    } else {
      if (!is_mixed)
        move_literals_to_watch ();
#ifndef NDEBUG
      if (!is_xor && !is_mixed) check_watched_literal_invariants ();
#endif
      //Find : Add clause lit
      int glue = (int) (learned_levels.size () + unassigned);
      //if (xor_clause_flag) printf("??? glue : %d\n",glue);
      assert (glue <= (int) clause.size ());
      bool clause_redundancy = from_propagator && ext_clause_forgettable;
      if (is_mixed) {
        mixed_clause_flag = true;
        // Restore saved block offsets for new_clause
        mixed_block_offsets.swap (saved_mixed_block_offsets);
      }
      if (is_xor) xor_clause_flag = true;  // set for new_clause()
      Clause *c = new_clause (clause_redundancy, glue); //Find : new clause
      xor_clause_flag = false;  // reset immediately
      mixed_clause_flag = false;
      // saved_mixed_block_offsets is cleared by swap above (now in mixed_block_offsets)
      // mixed_block_offsets will be cleared by new_clause's consumption
      //if (xor_clause_flag) printf("add new learned clause : %ld\n",new_id);
      c->id = new_id;
      clause_id--;

      //if (xor_clause_flag) printf("!!!\n");
      if (opts.unionset)
      {
        if (c->xor_flag && c->size <= 3)
        {
          AddXorGate(c);
        }
      }

      watch_clause (c);
      clause.clear ();
      original.clear ();
      handle_external_clause (c);
      newest_clause = c;
    }
  }
  clause.clear ();
  lrat_chain.clear ();
}

// Add learned new clause during conflict analysis and watch it. Requires
// that the clause is at least of size 2, and the first two literals
// are assigned at the highest decision level.
//
Clause *Internal::new_learned_redundant_clause (int glue) {
  assert (clause.size () > 1);
#ifndef NDEBUG
  for (size_t i = 2; i < clause.size (); i++)
    assert (var (clause[0]).level >= var (clause[i]).level),
        assert (var (clause[1]).level >= var (clause[i]).level);
#endif
  external->check_learned_clause ();
  Clause *res = new_clause (true, glue);
  if (proof) {
    proof->add_derived_clause (res, lrat_chain);
  }
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper binary resolved clause during 'probing'.
//
Clause *Internal::new_hyper_binary_resolved_clause (bool red, int glue) {
  external->check_learned_clause ();
  Clause *res = new_clause (red, glue);
  if (proof) {
    proof->add_derived_clause (res, lrat_chain);
  }
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add hyper ternary resolved clause during 'ternary'.
//
Clause *Internal::new_hyper_ternary_resolved_clause (bool red) {
  external->check_learned_clause ();
  size_t size = clause.size ();
  Clause *res = new_clause (red, size);
  if (proof) {
    proof->add_derived_clause (res, lrat_chain);
  }
  assert (!watching ());
  return res;
}

Clause *Internal::new_factor_clause (int witness) {
  external->check_learned_clause ();
  stats.factor_added++;
  stats.literals_factored += clause.size ();
  Clause *res = new_clause (false, 0);
  if (proof) {
    if (witness)
      proof->add_derived_rat_clause (res, externalize (witness),
                                     lrat_chain);
    else
      proof->add_derived_clause (res, lrat_chain);
  }
  assert (!watching ());
  assert (occurring ());
  for (const auto &lit : *res) {
    occs (lit).push_back (res);
  }
  return res;
}

// Add hyper ternary resolved clause during 'congruence' and watch it
//
Clause *
Internal::new_hyper_ternary_resolved_clause_and_watch (bool red,
                                                       bool full_watching) {
  external->check_learned_clause ();
  size_t size = clause.size ();
  Clause *res = new_clause (red, size);
  if (proof) {
    proof->add_derived_clause (res, lrat_chain);
  }
  if (full_watching) {
    assert (watching ());
    watch_clause (res);
  }
  return res;
}

// Add a new clause with same glue and redundancy as 'orig' but literals are
// assumed to be in 'clause' in 'decompose' and 'vivify'.
//
Clause *Internal::new_clause_as (const Clause *orig) {
  external->check_learned_clause ();
  const int new_glue = orig->glue;
  Clause *res = new_clause (orig->redundant, new_glue);
  if (proof) {
    proof->add_derived_clause (res, lrat_chain);
  }
  assert (watching ());
  watch_clause (res);
  return res;
}

// Add resolved clause during resolution, e.g., bounded variable
// elimination, but do not connect its occurrences here.
//
Clause *Internal::new_resolved_irredundant_clause () {
  external->check_learned_clause ();
  if (proof) {
    proof->add_derived_clause (clause_id + 1, false, clause, lrat_chain);
  }
  Clause *res = new_clause (false);
  assert (!watching ());
  return res;
}

void Internal::decay_clauses_upon_incremental_clauses () {
  if (!opts.incdecay)
    return;
  if (!stats.searches)
    return;
  if (stats.conflicts < lim.incremental_decay)
    return;

  PHASE ("decay", stats.incremental_decay,
         "decaying clauses with next decaying at conflict %" PRId64
         "(after the next incremental call)",
         lim.incremental_decay);

  for (auto c : clauses) {
    if (c->garbage)
      continue;
    if (!c->redundant)
      continue;
    if (c->id >= last.incremental_decay.last_id)
      continue;
    switch (opts.incdecay) {
    case 1: // my intuition
      ++c->glue;
      break;
    case 2: // Armin's idea
      if (c->glue < tier1[false])
        c->used = 1;
      break;
    case 3:
      if (c->glue < tier1[false])
        c->used = 1;
      ++c->glue;
      break;
    default:
      break;
    }
  }

  lim.incremental_decay += stats.conflicts + opts.incdecayint;
  ++stats.incremental_decay;
  last.incremental_decay.last_id = clause_id;
}
/*------------------------------------------------------------------------*/

// Build var_to_mixed index: maps each variable to the mixed clauses and
// block indices where it appears. Called after all clauses are parsed.
void Internal::build_var_to_mixed_index () {
  // Compact mixed_clauses (remove null entries)
  vector<Clause *> compact;
  for (auto c : mixed_clauses)
    if (c && !c->garbage)
      compact.push_back (c);
  mixed_clauses = compact;

  // Ensure var_to_mixed is large enough
  while ((int) var_to_mixed.size () <= max_var + 1)
    var_to_mixed.push_back ({});

  for (int ci = 0; ci < (int) mixed_clauses.size (); ci++) {
    Clause *c = mixed_clauses[ci];
    if (!c || c->garbage) continue;
    const int *offsets = c->block_offsets ();
    int nb = c->mixed_num_blocks;

    for (int bi = 0; bi < nb; bi++) {
      int bs = (bi == 0) ? 0 : offsets[bi - 1];
      int be = offsets[bi];

      for (int j = bs; j < be; j++) {
        int lit = c->literals[j];
        int v = abs (lit);
        while ((int) var_to_mixed.size () <= v)
          var_to_mixed.push_back ({});
        var_to_mixed[v].push_back ({ci, bi, lit});
        // Initialize parity from current assignments
        if (val (lit) > 0)
          c->mixed_parity ^= (1ULL << bi);
      }
    }
  }
}

void Internal::schedule_mixed_reconnect (Clause *c) {
  // Avoid duplicates
  for (auto existing : lost_mixed_watches)
    if (existing == c)
      return;
  lost_mixed_watches.push_back (c);
}

} // namespace CaDiCaL
