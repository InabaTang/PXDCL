#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Code for conflict analysis, i.e., to generate the first UIP clause.  The
// main function is 'analyze' below.  It further uses 'minimize' to minimize
// the first UIP clause, which is in 'minimize.cpp'.  An important side
// effect of conflict analysis is to update the decision queue by bumping
// variables.  Similarly analyzed clauses are bumped to mark them as active.

/*------------------------------------------------------------------------*/

void Internal::learn_empty_clause () {
  assert (!unsat);
  build_chain_for_empty ();
  LOG ("learned empty clause");
  external->check_learned_empty_clause ();
  int64_t id = ++clause_id;
  if (proof) {
    proof->add_derived_empty_clause (id, lrat_chain);
  }
  unsat = true;
  conflict_id = id;
  marked_failed = true;
  conclusion.push_back (id);
  lrat_chain.clear ();
}

void Internal::learn_unit_clause (int lit) {
  assert (!unsat);
  LOG ("learned unit clause %d, stored at position %d", lit, vlit (lit));
  external->check_learned_unit_clause (lit);
  int64_t id = ++clause_id;
  if (lrat || frat) {
    const unsigned uidx = vlit (lit);
    unit_clauses (uidx) = id;
  }
  if (proof) {
    proof->add_derived_unit_clause (id, lit, lrat_chain);
  }
  mark_fixed (lit);
}

/*------------------------------------------------------------------------*/

// Move bumped variables to the front of the (VMTF) decision queue.  The
// 'bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

void Internal::bump_queue (int lit) {
  assert (opts.bump);
  const int idx = vidx (lit);
  if (!links[idx].next)
    return;
  queue.dequeue (links, idx);
  queue.enqueue (links, idx);
  assert (stats.bumped != INT64_MAX);
  btab[idx] = ++stats.bumped;
  LOG ("moved to front variable %d and bumped to %" PRId64 "", idx,
       btab[idx]);
  if (!vals[idx])
    update_queue_unassigned (idx);
}

/*------------------------------------------------------------------------*/

// It would be better to use 'isinf' but there are some historical issues
// with this function.  On some platforms it is a macro and even for C++ it
// changed the scope (in pre 5.0 gcc) from '::isinf' to 'std::isinf'.  I do
// not want to worry about these strange incompatibilities and thus use the
// same trick as in older solvers (since the MiniSAT team invented EVSIDS)
// and simply put a hard limit here.  It is less elegant but easy to port.

static inline bool evsids_limit_hit (double score) {
  assert (sizeof (score) == 8); // assume IEEE 754 64-bit double
  return score > 1e150;         // MAX_DOUBLE is around 1.8e308
}

/*------------------------------------------------------------------------*/

// Classical exponential VSIDS as pioneered by MiniSAT.

void Internal::rescale_variable_scores () {
  stats.rescored++;
  double divider = score_inc;
  for (auto idx : vars) {
    const double tmp = stab[idx];
    if (tmp > divider)
      divider = tmp;
  }
  PHASE ("rescore", stats.rescored, "rescoring %d variable scores by 1/%g",
         max_var, divider);
  assert (divider > 0);
  double factor = 1.0 / divider;
  for (auto idx : vars)
    stab[idx] *= factor;
  score_inc *= factor;
  PHASE ("rescore", stats.rescored,
         "new score increment %g after %" PRId64 " conflicts", score_inc,
         stats.conflicts);
}

void Internal::bump_variable_score (int lit) {
  assert (opts.bump);
  int idx = vidx (lit);
  double old_score = score (idx);
  assert (!evsids_limit_hit (old_score));
  double new_score = old_score + score_inc;
  if (evsids_limit_hit (new_score)) {
    LOG ("bumping %g score of %d hits EVSIDS score limit", old_score, idx);
    rescale_variable_scores ();
    old_score = score (idx);
    assert (!evsids_limit_hit (old_score));
    new_score = old_score + score_inc;
  }
  assert (!evsids_limit_hit (new_score));
  LOG ("new %g score of %d", new_score, idx);
  score (idx) = new_score;
  if (scores.contains (idx))
    scores.update (idx);
}

// Important variables recently used in conflict analysis are 'bumped',

void Internal::bump_variable (int lit) {
  if (use_scores ())
    bump_variable_score (lit);
  else
    bump_queue (lit);
}

// After every conflict the variable score increment is increased by a
// factor (if we are currently using scores).

void Internal::bump_variable_score_inc () {
  assert (use_scores ());
  assert (!evsids_limit_hit (score_inc));
  double f = 1e3 / opts.scorefactor;
  double new_score_inc = score_inc * f;
  if (evsids_limit_hit (new_score_inc)) {
    LOG ("bumping %g increment by %g hits EVSIDS score limit", score_inc,
         f);
    rescale_variable_scores ();
    new_score_inc = score_inc * f;
  }
  assert (!evsids_limit_hit (new_score_inc));
  LOG ("bumped score increment from %g to %g with factor %g", score_inc,
       new_score_inc, f);
  score_inc = new_score_inc;
}

/*------------------------------------------------------------------------*/

struct analyze_bumped_rank {
  Internal *internal;
  analyze_bumped_rank (Internal *i) : internal (i) {}
  typedef uint64_t Type;
  Type operator() (const int &a) const { return internal->bumped (a); }
};

struct analyze_bumped_smaller {
  Internal *internal;
  analyze_bumped_smaller (Internal *i) : internal (i) {}
  bool operator() (const int &a, const int &b) const {
    const auto s = analyze_bumped_rank (internal) (a);
    const auto t = analyze_bumped_rank (internal) (b);
    return s < t;
  }
};

/*------------------------------------------------------------------------*/

void Internal::bump_variables () {

  assert (opts.bump);

  START (bump);

  if (!use_scores ()) {

    // Variables are bumped in the order they are in the current decision
    // queue.  This maintains relative order between bumped variables in
    // the queue and seems to work best.  We also experimented with
    // focusing on variables of the last decision level, but results were
    // mixed.

    MSORT (opts.radixsortlim, analyzed.begin (), analyzed.end (),
           analyze_bumped_rank (this), analyze_bumped_smaller (this));
  }

  for (const auto &lit : analyzed)
    bump_variable (lit);

  if (use_scores ())
    bump_variable_score_inc ();

  STOP (bump);
}

/*------------------------------------------------------------------------*/

// We use the glue time stamp table 'gtab' for fast glue computation.

int Internal::recompute_glue (Clause *c) {
  int res = 0;
  const int64_t stamp = ++stats.recomputed;
  for (const auto &lit : *c) {
    assert (val (lit));
    int level = var (lit).level;
    assert (gtab[level] <= stamp);
    if (gtab[level] == stamp)
      continue;
    gtab[level] = stamp;
    res++;
  }
  return res;
}

// Clauses resolved since the last reduction are marked as 'used', their
// glue is recomputed and they are promoted if the glue shrinks.  Note that
// promotion from 'tier3' to 'tier2' will set 'used' to '2'.

inline void Internal::bump_clause (Clause *c) {
  LOG (c, "bumping");
  c->used = max_used;
  if (c->hyper)
    return;
  if (!c->redundant)
    return;
  int new_glue = recompute_glue (c);
  if (new_glue < c->glue)
    promote_clause (c, new_glue);

  const size_t glue =
      std::min ((size_t) c->glue, stats.used[stable].size () - 1);
  ++stats.used[stable][glue];
  ++stats.bump_used[stable];
}

void Internal::bump_clause2 (Clause *c) { bump_clause (c); }
/*------------------------------------------------------------------------*/

// During conflict analysis literals not seen yet either become part of the
// first unique implication point (UIP) clause (if on lower decision level),
// are dropped (if fixed), or are resolved away (if on the current decision
// level and different from the first UIP).  At the same time we update the
// number of seen literals on a decision level.  This helps conflict clause
// minimization.  The number of seen levels is the glucose level (also
// called 'glue', or 'LBD').

inline void Internal::analyze_literal (int lit, int &open,
                                       int &resolvent_size,
                                       int &antecedent_size) {
  assert (lit);
  Var &v = var (lit);
  Flags &f = flags (lit);

  if (!v.level) {
    if (f.seen || !lrat)
      return;
    f.seen = true;
    unit_analyzed.push_back (lit);
    assert (val (lit) < 0);
    int64_t id = unit_id (-lit);
    unit_chain.push_back (id);
    return;
  }
  ++antecedent_size;
  if (f.seen)
    return;

  // before marking as seen, get reason and check for missed unit

  //printf("v.level = %d , level = %d , lit = %d\n",v.level,level,lit);

  assert (val (lit) < 0);
  assert (v.level <= level);
  if (v.reason == external_reason) {
    assert (!opts.exteagerreasons);
    v.reason = learn_external_reason_clause (-lit, 0, true);
    if (!v.reason) { // actually a unit
      --antecedent_size;
      LOG ("%d unit after explanation", -lit);
      if (f.seen || !lrat)
        return;
      f.seen = true;
      unit_analyzed.push_back (lit);
      assert (val (lit) < 0);
      const unsigned uidx = vlit (-lit);
      int64_t id = unit_clauses (uidx);
      assert (id);
      unit_chain.push_back (id);
      return;
    }
  }

  f.seen = true;
  analyzed.push_back (lit);

  assert (v.reason != external_reason);
  if (v.level < level)
    clause.push_back (lit);
  Level &l = control[v.level];
  if (!l.seen.count++) {
    LOG ("found new level %d contributing to conflict", v.level);
    levels.push_back (v.level);
  }
  if (v.trail < l.seen.trail)
    l.seen.trail = v.trail;
  ++resolvent_size;
  LOG ("analyzed literal %d assigned at level %d", lit, v.level);
  if (v.level == level)
    open++;
}

inline void Internal::analyze_reason (int lit, Clause *reason, int &open,
                                      int &resolvent_size,
                                      int &antecedent_size) {
  assert (reason);
  assert (reason != external_reason);
  if (!reason) return;
  bump_clause (reason);
  if (lrat)
    lrat_chain.push_back (reason->id);
  //printf("lits is : %d ",lit); pri_val_clause(reason);
  if (reason -> xor_flag)
  {
    // XOR-style flipping for XOR clauses (original behavior).
    // Build a flipped copy instead of mutating the clause in-place.
    vector<int> flipped;
    flipped.reserve (reason->size);
    bool left = false;
    for (const auto &other : *reason) {
      int v = val (other);
      if (v > 0) {
        flipped.push_back (-other);
        left ^= true;
      } else if (v < 0) {
        flipped.push_back (other);
      } else {
        flipped.push_back (other);
      }
    }
    if (left) {
      for (auto &other : flipped) {
        if (abs (other) == abs (lit)) {
          assert (val (other) < 0);
          other = -other;
          left ^= true;
        }
      }
    }
    assert (!left);
    for (const auto &other : flipped)
      if (abs (other) != abs (lit))
        analyze_literal (other, open, resolvent_size, antecedent_size);
  }
  else if (reason->mixed_flag)
  {
    // Phase-1 mixed candidate construction (algorithm-3 attempt):
    // for the initial mixed conflict expansion (lit == 0), project the
    // conflict to violated blocks only and cap candidate growth.  If any
    // guard fails we fall back to the existing stable XOR-style path.
    const int mixedcand_mode = opts.mixedcand;
    size_t mixed_candidate_limit = 0;
    int mixed_reason_size_limit = 0;
    int mixed_block_limit = 0;
    if (mixedcand_mode == 1) {
      mixed_candidate_limit = 192;
      mixed_reason_size_limit = 64;
      mixed_block_limit = 8;
    } else if (mixedcand_mode == 2) {
      mixed_candidate_limit = 384;
      mixed_reason_size_limit = 128;
      mixed_block_limit = 16;
    }

    if (!lit && mixed_candidate_limit > 0 && reason->mixed_num_blocks > 0 &&
        reason->size <= mixed_reason_size_limit &&
        reason->mixed_num_blocks <= mixed_block_limit) {
      const int *offsets = reason->block_offsets ();
      const int nb = reason->mixed_num_blocks;

      bool complete = true;
      std::vector<int> candidate;
      candidate.reserve (reason->size);

      for (int bi = 0; bi < nb; bi++) {
        const int bs = (bi == 0) ? 0 : offsets[bi - 1];
        const int be = offsets[bi];
        if (bs < 0 || be < bs || be > reason->size) {
          complete = false;
          break;
        }

        bool parity = false;
        for (int j = bs; j < be; j++) {
          const int orig = reason->literals[j];
          const signed char v = val (orig);
          if (!v) {
            complete = false;
            break;
          }
          if (v > 0)
            parity = !parity;
        }
        if (!complete)
          break;

        if (parity)
          continue; // satisfied block, irrelevant for violated-block reason

        for (int j = bs; j < be; j++) {
          int other = reason->literals[j];
          if (val (other) > 0)
            other = -other; // normalize to currently false literal
          candidate.push_back (other);
        }
        if (candidate.size () > mixed_candidate_limit) {
          complete = false;
          break;
        }
      }

      if (complete && !candidate.empty ()) {
        std::sort (candidate.begin (), candidate.end (),
                   [] (int a, int b) {
                     return abs (a) < abs (b)
                            || (abs (a) == abs (b) && a < b);
                   });
        int last = 0;
        for (const auto &other : candidate) {
          if (last && other == last)
            continue;
          if (flags (other).seen)
            continue;
          last = other;
          analyze_literal (other, open, resolvent_size, antecedent_size);
        }
        return;
      }
    }

    // XOR-style flipping for mixed clauses (same logic as XOR).
    // Convert all TRUE literals to FALSE using the 'left' flag to track
    // parity.  The flipped clause produces an all-FALSE representation
    // needed for analyze_literal.  For the pivot: skip all occurrences
    // with the same abs value (a variable can appear in multiple blocks,
    // but the pivot's parity adjustment via the 'left' flag handles the
    // block-level parity correctly for the specific propagation).
    vector<int> flipped;
    flipped.reserve (reason->size);
    bool left = false;
    for (const auto &other : *reason) {
      int v = val (other);
      if (v > 0) {
        flipped.push_back (-other);
        left ^= true;
      } else if (v < 0) {
        flipped.push_back (other);
      } else {
        flipped.push_back (other);
      }
    }
    if (left) {
      for (auto &other : flipped) {
        if (abs (other) == abs (lit)) {
          assert (val (other) < 0);
          other = -other;
          left ^= true;
        }
      }
    }
    assert (!left);
    sort (flipped.begin (), flipped.end (),
          [](int a, int b) { return abs (a) < abs (b)
                             || (abs (a) == abs (b) && a < b); });
    int last = 0;
    for (const auto &other : flipped) {
      if (abs (other) == abs (lit)) continue;
      if (last && other == last) continue;
      if (flags (other).seen) continue;
      last = other;
      analyze_literal (other, open, resolvent_size, antecedent_size);
    }
  }
  else
  {
    //printf("??? lit = %d\n");
    for (const auto &other : *reason)
      if (other != lit)
        analyze_literal (other, open, resolvent_size, antecedent_size);
  }
  //printf("why? open is %d\n",open);
}

/*------------------------------------------------------------------------*/

// Conservative XOR-UIP candidate generation.
//
// This routine never mutates solver state and only builds a candidate OR
// clause from a pure XOR-reason closure around the current UIP literal.
// If any guard fails, it returns false and the caller must keep baseline.

bool Internal::try_xor_uip_clause (int uip, const std::vector<int> &baseline,
                                   std::vector<int> &out) {
  out.clear ();
  if (!opts.xoruip)
    return false;
  // Replacing the baseline 1-UIP clause requires rebuilding the proof chain.
  // Until that is implemented, keep proof/check modes on the baseline path.
  if (proof)
    return false;
  if (!uip)
    return false;
  if (baseline.size () < 2)
    return false;
  if (var (uip).level != level)
    return false;

  // Gather XOR-reason cone from current-level literals in baseline.
  std::vector<int> stack;
  std::vector<int> topo;
  std::unordered_set<int> in_cone;
  stack.reserve (baseline.size () + 16);
  topo.reserve (baseline.size () + 32);
  in_cone.reserve (baseline.size () + 64);

  for (const int lit : baseline) {
    if (lit == -uip)
      continue;
    if (var (lit).level != level)
      continue;
    stack.push_back (-lit);
  }

  const size_t xor_depth_cap = 96;
  const size_t xor_nodes_cap = 512;
  size_t depth = 0;

  while (!stack.empty ()) {
    if (++depth > xor_depth_cap)
      return false;
    const int lit = stack.back ();
    stack.pop_back ();
    if (in_cone.find (lit) != in_cone.end ())
      continue;
    in_cone.insert (lit);
    topo.push_back (lit);
    if (topo.size () > xor_nodes_cap)
      return false;

    Var &v = var (lit);
    Clause *r = v.reason;
    if (!r || r == external_reason)
      continue;
    if (!r->xor_flag || r->mixed_flag)
      return false; // strict: only pure XOR reasons in closure

    for (const int other : *r) {
      if (abs (other) == abs (lit))
        continue;
      if (val (other) >= 0)
        return false;
      if (var (other).level == level &&
          in_cone.find (other) == in_cone.end ())
        stack.push_back (other);
    }
  }

  if (topo.empty ())
    return false;

  // XOR-eliminate internal current-level literals from baseline.
  std::vector<int> parity_clause = baseline;
  for (const int lit : topo) {
    Var &v = var (lit);
    Clause *r = v.reason;
    if (!r || r == external_reason)
      continue;

    std::vector<int> row;
    row.reserve (r->size);
    bool left = false;
    for (const int other : *r) {
      const int vv = val (other);
      if (vv > 0) {
        row.push_back (-other);
        left ^= true;
      } else if (vv < 0) {
        row.push_back (other);
      } else {
        return false;
      }
    }
    if (left) {
      bool fixed = false;
      for (auto &x : row) {
        if (abs (x) == abs (lit)) {
          x = -x;
          fixed = true;
          left ^= true;
          break;
        }
      }
      if (!fixed || left)
        return false;
    }

    parity_clause.push_back (-lit);
    for (const int x : row)
      if (abs (x) != abs (lit))
        parity_clause.push_back (x);
  }

  // Reduce mod-2 multiplicity.
  std::sort (parity_clause.begin (), parity_clause.end (),
             [] (int a, int b) {
               return abs (a) < abs (b)
                      || (abs (a) == abs (b) && a < b);
             });

  out.reserve (parity_clause.size ());
  for (size_t i = 0; i < parity_clause.size ();) {
    const int lit = parity_clause[i];
    size_t j = i + 1;
    while (j < parity_clause.size () && parity_clause[j] == lit)
      j++;
    if (((j - i) & 1) == 1)
      out.push_back (lit);
    i = j;
  }

  if (out.empty ())
    return false;

  // Tautology check and normalization.
  std::sort (out.begin (), out.end (),
             [] (int a, int b) {
               return abs (a) < abs (b)
                      || (abs (a) == abs (b) && a < b);
             });
  for (size_t i = 1; i < out.size (); i++) {
    if (out[i] == out[i - 1]) {
      out.erase (out.begin () + i);
      i--;
      continue;
    }
    if (out[i] == -out[i - 1]) {
      out.clear ();
      return false;
    }
  }

  // Must contain -uip exactly once and no other current-level literals.
  int uip_count = 0;
  for (const int lit : out) {
    if (lit == -uip)
      uip_count++;
    else if (var (lit).level == level)
      return false;
    if (val (lit) >= 0)
      return false; // learned clause should be asserting now
  }
  if (uip_count != 1)
    return false;

  // Keep memory/runtime bounded and avoid growth regressions.
  if (out.size () > baseline.size () + 8)
    return false;
  if (out.size () > 256)
    return false;

  return true;
}

/*------------------------------------------------------------------------*/

// This is an idea which was implicit in MapleCOMSPS 2016 for 'limit = 1'.
// See also the paragraph on 'bumping reason side literals' in their SAT'16
// paper [LiangGaneshPoupartCzarnecki-SAT'16].  Reason side bumping was
// performed exactly when 'LRB' based decision heuristics was used, which in
// the original version was enabled after 10000 conflicts until a time limit
// of 2500 seconds was reached (half of the competition time limit).  The
// Maple / Glucose / MiniSAT evolution winning the SAT race in 2019 made
// the schedule of reason side bumping deterministic, i.e., avoiding a time
// limit, by switching between 'LRB' and 'VSIDS' in an interval of initially
// 30 million propagations, which then is increased geometrically by 10%.

inline bool Internal::bump_also_reason_literal (int lit) {
  assert (lit);
  assert (val (lit) < 0);
  Flags &f = flags (lit);
  if (f.seen)
    return false;
  const Var &v = var (lit);
  if (!v.level)
    return false;
  f.seen = true;
  analyzed.push_back (lit);
  LOG ("bumping also reason literal %d assigned at level %d", lit, v.level);
  return true;
}

// We experimented with deeper reason bumping without much success though.

inline void Internal::bump_also_reason_literals (int lit, int depth_limit,
                                                 size_t analyzed_limit) {
  assert (lit);
  assert (depth_limit > 0);
  const Var &v = var (lit);
  assert (val (lit));
  if (!v.level)
    return;
  Clause *reason = v.reason;
  if (!reason || reason == external_reason)
    return;
  stats.ticks.search[stable]++;
  for (const auto &other : *reason) {
    if (other == lit)
      continue;
    if (!bump_also_reason_literal (other))
      continue;
    if (depth_limit < 2)
      continue;
    bump_also_reason_literals (-other, depth_limit - 1, analyzed_limit);
    if (analyzed.size () > analyzed_limit)
      break;
  }
}

inline void Internal::bump_also_all_reason_literals () {
  assert (opts.bump);
  if (!opts.bumpreason)
    return;
  if (averages.current.decisions > opts.bumpreasonrate) {
    LOG ("decisions per conflict rate %g > limit %d",
         (double) averages.current.decisions, opts.bumpreasonrate);
    return;
  }
  if (delay[stable].bumpreasons.limit) {
    LOG ("delaying reason bumping %" PRId64 " more times",
         delay[stable].bumpreasons.limit);
    delay[stable].bumpreasons.limit--;
    return;
  }
  assert (opts.bumpreasondepth > 0);
  const int depth_limit = opts.bumpreasondepth + stable;
  size_t saved_analyzed = analyzed.size ();
  size_t analyzed_limit = saved_analyzed * opts.bumpreasonlimit;
  for (const auto &lit : clause)
    if (analyzed.size () <= analyzed_limit)
      bump_also_reason_literals (-lit, depth_limit, analyzed_limit);
    else
      break;
  if (analyzed.size () > analyzed_limit) {
    LOG ("not bumping reason side literals as limit exhausted");
    for (size_t i = saved_analyzed; i != analyzed.size (); i++) {
      const int lit = analyzed[i];
      Flags &f = flags (lit);
      assert (f.seen);
      f.seen = false;
    }
    delay[stable].bumpreasons.interval++;
    analyzed.resize (saved_analyzed);
  } else {
    LOG ("bumping reasons up to depth %d", opts.bumpreasondepth);
    delay[stable].bumpreasons.interval /= 2;
  }
  LOG ("delay internal %" PRId64, delay[stable].bumpreasons.interval);
  delay[stable].bumpreasons.limit = delay[stable].bumpreasons.interval;
}

/*------------------------------------------------------------------------*/

void Internal::clear_unit_analyzed_literals () {
  LOG ("clearing %zd unit analyzed literals", unit_analyzed.size ());
  for (const auto &lit : unit_analyzed) {
    Flags &f = flags (lit);
    assert (f.seen);
    assert (!var (lit).level);
    f.seen = false;
    assert (!f.keep);
    assert (!f.poison);
    assert (!f.removable);
  }
  unit_analyzed.clear ();
}

void Internal::clear_analyzed_literals () {
  LOG ("clearing %zd analyzed literals", analyzed.size ());
  for (const auto &lit : analyzed) {
    Flags &f = flags (lit);
    assert (f.seen);
    f.seen = false;
    assert (!f.keep);
    assert (!f.poison);
    assert (!f.removable);
  }
  analyzed.clear ();
#if 0 // to expensive, even for debugging mode
  if (unit_analyzed.size ())
    return;
  for (auto idx : vars) {
    Flags &f = flags (idx);
    assert (!f.seen);
  }
#endif
}

void Internal::clear_analyzed_levels () {
  LOG ("clearing %zd analyzed levels", levels.size ());
  for (const auto &l : levels)
    if (l < (int) control.size ())
      control[l].reset ();
  levels.clear ();
}

/*------------------------------------------------------------------------*/

// Smaller level and trail.  Comparing literals on their level is necessary
// for chronological backtracking, since trail order might in this case not
// respect level order.

struct analyze_trail_negative_rank {
  Internal *internal;
  analyze_trail_negative_rank (Internal *s) : internal (s) {}
  typedef uint64_t Type;
  Type operator() (int a) {
    Var &v = internal->var (a);
    uint64_t res = v.level;
    res <<= 32;
    res |= v.trail;
    return ~res;
  }
};

struct analyze_trail_larger {
  Internal *internal;
  analyze_trail_larger (Internal *s) : internal (s) {}
  bool operator() (const int &a, const int &b) const {
    return analyze_trail_negative_rank (internal) (a) <
           analyze_trail_negative_rank (internal) (b);
  }
};

/*------------------------------------------------------------------------*/

// Generate new driving clause and compute jump level.

Clause *Internal::new_driving_clause (const int glue, int &jump) {

  const size_t size = clause.size ();
  Clause *res;

  if (!size) {

    jump = 0;
    res = 0;

  } else if (size == 1) {

    iterating = true;
    jump = 0;
    res = 0;

  } else {

    assert (clause.size () > 1);

    // We have to get the last assigned literals into the watch position.
    // Sorting all literals with respect to reverse assignment order is
    // overkill but seems to get slightly faster run-time.  For 'minimize'
    // we sort the literals too heuristically along the trail order (so in
    // the opposite order) with the hope to hit the recursion limit less
    // frequently.  Thus sorting effort is doubled here.
    //
    MSORT (opts.radixsortlim, clause.begin (), clause.end (),
           analyze_trail_negative_rank (this), analyze_trail_larger (this));

    jump = var (clause[1]).level;
    res = new_learned_redundant_clause (glue);
    res->used = max_used;
  }

  LOG ("jump level %d", jump);

  return res;
}

/*------------------------------------------------------------------------*/

// determine the OTFS level for OTFS. Unlike the find_conflict_level, we do
// not have to fix the clause

inline int Internal::otfs_find_backtrack_level (int &forced) {
  assert (opts.otfs);
  int res = 0;

  for (const auto &lit : *conflict) {
    const int tmp = var (lit).level;
    if (tmp == level) {
      forced = lit;
    } else if (tmp > res) {
      res = tmp;
      LOG ("bt level is now %d due to %d", res, lit);
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

// If chronological backtracking is enabled we need to find the actual
// conflict level and then potentially can also reuse the conflict clause
// as driving clause instead of deriving a redundant new driving clause
// (forcing 'forced') if the number 'count' of literals in conflict assigned
// at the conflict level is exactly one.

inline int Internal::find_conflict_level (int &forced) {

  assert (conflict);
  assert (opts.chrono || opts.otfs || external_prop);

  int res = 0, count = 0;

  forced = 0;

  //printf("into back 2 conflict is :"); if (conflict) pri_val_clause(conflict);
  for (const auto &lit : *conflict) {
    const int tmp = var (lit).level;
    if (tmp > res) {
      res = tmp;
      forced = lit;
      count = 1;
    } else if (tmp == res) {
      count++;
      if (res == level && count > 1)
        break;
    }
  }

  LOG ("%d literals on actual conflict level %d", count, res);
  // printf ("%d literals on actual conflict level %d", count, res);

  const int size = conflict->size;
  int *lits = conflict->literals;

  // Skip reordering for mixed and XOR clauses:
  // - Mixed: block offsets must be preserved
  // - XOR: watch positions (lits[0], lits[1]) must be preserved
  if (conflict->mixed_flag || conflict->xor_flag) {
    if (count > 1) forced = 0;
    return res;
  }

  // Move the two highest level literals to the front.
  //
  for (int i = 0; i < 2; i++) {

    const int lit = lits[i];

    int highest_position = i;
    int highest_literal = lit;
    int highest_level = var (highest_literal).level;

    for (int j = i + 1; j < size; j++) {
      const int other = lits[j];
      const int tmp = var (other).level;
      if (highest_level >= tmp)
        continue;
      highest_literal = other;
      highest_position = j;
      highest_level = tmp;
      if (highest_level == res)
        break;
    }

    // No unwatched higher assignment level literal.
    //
    if (highest_position == i)
      continue;

    if (highest_position > 1) {
      LOG (conflict, "unwatch %d in", lit);
      if (conflict->xor_conflict_flag)
      {
        //do nothing
      }
      else if (conflict->mixed_flag) {
        remove_mixed_watch (mixed_watches (lit), conflict);
      }
      else if (conflict->xor_flag) {
        remove_watch (xor_watches (lit), conflict);
      } else {
        remove_watch (watches (lit), conflict);
      }
    }

    lits[highest_position] = lit;
    lits[i] = highest_literal;

    if (highest_position > 1)
    {
      if (conflict->xor_conflict_flag)
      {
        //do nothing
      }
      else if (conflict->mixed_flag) {
        watch_mixed_literal (highest_literal, lits[!i], conflict);
      } else if (conflict->xor_flag) {
        watch_xor_literal (highest_literal, lits[!i], conflict);
      } else {
        watch_literal (highest_literal, lits[!i], conflict);
      }
    }
  }

  // Only if the number of highest level literals in the conflict is one
  // then we can reuse the conflict clause as driving clause for 'forced'.
  //
  if (count != 1)
    forced = 0;

  return res;
}

/*------------------------------------------------------------------------*/

inline int Internal::determine_actual_backtrack_level (int jump) {

  int res;

  assert (level > jump);

  if (!opts.chrono) {
    res = jump;
    LOG ("chronological backtracking disabled using jump level %d", res);
  } else if (opts.chronoalways) {
    stats.chrono++;
    res = level - 1;
    LOG ("forced chronological backtracking to level %d", res);
  } else if (jump >= level - 1) {
    res = jump;
    LOG ("jump level identical to chronological backtrack level %d", res);
  } else if ((size_t) jump < assumptions.size ()) {
    res = jump;
    LOG ("using jump level %d since it is lower than assumption level %zd",
         res, assumptions.size ());
  } else if (level - jump > opts.chronolevelim) {
    stats.chrono++;
    res = level - 1;
    LOG ("back-jumping over %d > %d levels prohibited"
         "thus backtracking chronologically to level %d",
         level - jump, opts.chronolevelim, res);
  } else if (opts.chronoreusetrail) {
    int best_idx = 0, best_pos = 0;

    if (use_scores ()) {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && !score_smaller (this) (best_idx, idx))
          continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable score %g", score (best_idx));
    } else {
      for (size_t i = control[jump + 1].trail; i < trail.size (); i++) {
        const int idx = abs (trail[i]);
        if (best_idx && bumped (best_idx) >= bumped (idx))
          continue;
        best_idx = idx;
        best_pos = i;
      }
      LOG ("best variable bumped %" PRId64 "", bumped (best_idx));
    }
    assert (best_idx);
    LOG ("best variable %d at trail position %d", best_idx, best_pos);

    // Now find the frame and decision level in the control stack of that
    // best variable index.  Note that, as in 'reuse_trail', the frame
    // 'control[i]' for decision level 'i' contains the trail before that
    // decision level, i.e., the decision 'control[i].decision' sits at
    // 'control[i].trail' in the trail and we thus have to check the level
    // of the control frame one higher than at the result level.
    //
    res = jump;
    while (res < level - 1 && control[res + 1].trail <= best_pos)
      res++;

    if (res == jump)
      LOG ("default non-chronological back-jumping to level %d", res);
    else {
      stats.chrono++;
      LOG ("chronological backtracking to level %d to reuse trail", res);
    }

  } else {
    res = jump;
    LOG ("non-chronological back-jumping to level %d", res);
  }

  return res;
}

/*------------------------------------------------------------------------*/

void Internal::eagerly_subsume_recently_learned_clauses (Clause *c) {
  assert (opts.eagersubsume);
  LOG (c, "trying eager subsumption with");
  mark (c);
  int64_t lim = stats.eagertried + opts.eagersubsumelim;
  const auto begin = clauses.begin ();
  auto it = clauses.end ();
#ifdef LOGGING
  int64_t before = stats.eagersub;
#endif
  while (it != begin && stats.eagertried++ <= lim) {
    Clause *d = *--it;
    if (c == d)
      continue;
    if (d->garbage)
      continue;
    if (!d->redundant)
      continue;
    int needed = c->size;
    for (auto &lit : *d) {
      if (marked (lit) <= 0)
        continue;
      if (!--needed)
        break;
    }
    if (needed)
      continue;
    LOG (d, "eager subsumed");
    stats.eagersub++;
    stats.subsumed++;
    mark_garbage (d);
  }
  unmark (c);
#ifdef LOGGING
  uint64_t subsumed = stats.eagersub - before;
  if (subsumed)
    LOG ("eagerly subsumed %" PRIu64 " clauses", subsumed);
#endif
}

/*------------------------------------------------------------------------*/

Clause *Internal::on_the_fly_strengthen (Clause *new_conflict, int uip) {
  assert (new_conflict);
  assert (new_conflict->size > 2);
  LOG (new_conflict, "applying OTFS on lit %d", uip);
  auto sorted = std::vector<int> ();
  sorted.reserve (new_conflict->size);
  assert (sorted.empty ());
  ++stats.otfs.strengthened;

  int *lits = new_conflict->literals;

  assert (abs(lits[0]) == abs(uip) || abs(lits[1]) == abs(uip));

  int other_init;
  if (abs(lits[0]) == abs(uip))
  {
    other_init = lits[1];
  }
  else
  {
    other_init = lits[0];
  }

  assert (mini_chain.empty ());

  const int old_size = new_conflict->size;
  int new_size = 0;
  for (int i = 0; i < old_size; ++i) {
    const int other = lits[i];
    sorted.push_back (other);
    if (var (other).level)
      lits[new_size++] = other;
  }

  LOG (new_conflict, "removing all units in");

  assert (abs(lits[0]) == abs(uip) || abs(lits[1]) == abs(uip));
  int other;
  if (abs(lits[0]) == abs(uip))
  {
    other = lits[1];
  }
  else
  {
    other = lits[0];
  }
  lits[0] = other;
  lits[1] = lits[--new_size];
  LOG (new_conflict, "putting uip at pos 1");

  if (other_init != other)
  {
    if (new_conflict->xor_flag) remove_watch (xor_watches (other_init), new_conflict);
    else remove_watch (watches (other_init), new_conflict);
  }
  if (new_conflict->xor_flag) (xor_watches (uip), new_conflict);
  else remove_watch (watches (uip), new_conflict);

  assert (!lrat || lrat_chain.back () == new_conflict->id);
  if (lrat) {
    assert (!lrat_chain.empty ());
    for (const auto &id : unit_chain) {
      mini_chain.push_back (id);
    }
    const auto end = lrat_chain.rend ();
    const auto begin = lrat_chain.rbegin ();
    for (auto i = begin; i != end; i++) {
      const auto id = *i;
      mini_chain.push_back (id);
    }
    lrat_chain.clear ();
    clear_unit_analyzed_literals ();
    unit_chain.clear ();
  }
  assert (unit_analyzed.empty ());
  // sort the clause
  {
    int highest_pos = 0;
    int highest_level = 0;
    for (int i = 1; i < new_size; i++) {
      const unsigned other = lits[i];
      assert (val (other) < 0);
      const int level = var (other).level;
      assert (level);
      LOG ("checking %d", other);
      if (level <= highest_level)
        continue;
      highest_pos = i;
      highest_level = level;
    }
    LOG ("highest lit is %d", lits[highest_pos]);
    if (highest_pos != 1)
      swap (lits[1], lits[highest_pos]);
    LOG ("removing %d literals", new_conflict->size - new_size);

    if (new_size == 1) {
      LOG (new_conflict, "new size = 1, so interrupting");
      assert (!opts.exteagerreasons);
      return 0;
    } else {
      otfs_strengthen_clause (new_conflict, uip, new_size, sorted);
      assert (new_size == new_conflict->size);
    }
  }

  if (other_init != other)
    watch_literal (other, lits[1], new_conflict);
  else {
    update_watch_size (watches (other), lits[1], new_conflict);
  }
  watch_literal (lits[1], other, new_conflict);

  LOG (new_conflict, "strengthened clause by OTFS");
  sorted.clear ();

  return new_conflict;
}

/*------------------------------------------------------------------------*/
inline void Internal::otfs_subsume_clause (Clause *subsuming,
                                           Clause *subsumed) {
  stats.subsumed++;
  assert (subsuming->size <= subsumed->size);
  LOG (subsumed, "subsumed");
  if (subsumed->redundant)
    stats.subred++;
  else
    stats.subirr++;
  if (subsumed->redundant || !subsuming->redundant) {
    mark_garbage (subsumed);
    return;
  }
  LOG ("turning redundant subsuming clause into irredundant clause");
  subsuming->redundant = false;
  if (proof)
    proof->strengthen (subsuming->id);
  mark_garbage (subsumed);
  stats.current.irredundant++;
  stats.added.irredundant++;
  stats.irrlits += subsuming->size;
  assert (stats.current.redundant > 0);
  stats.current.redundant--;
  assert (stats.added.redundant > 0);
  stats.added.redundant--;
  // ... and keep 'stats.added.total'.
}

/*------------------------------------------------------------------------*/

// Candidate clause 'c' is strengthened by removing 'lit' and units.
//
void Internal::otfs_strengthen_clause (Clause *c, int lit, int new_size,
                                       const std::vector<int> &old) {
  stats.strengthened++;
  assert (c->size > 2);
  (void) shrink_clause (c, new_size);
  if (proof) {
    proof->otfs_strengthen_clause (c, old, mini_chain);
  }
  if (!c->redundant) {
    mark_removed (lit);
  }
  mini_chain.clear ();
  c->used = max_used;
  LOG (c, "strengthened");
  external->check_shrunken_clause (c);
}

/*------------------------------------------------------------------------*/

// If the average number of decisions per conflict (analysis actually so not
// taking OTFS conflicts into account) is high we do not bump reasons. This
// is the function which updates the exponential moving decision rate
// average.

void Internal::update_decision_rate_average () {
  int64_t current = stats.decisions;
  int64_t decisions = current - saved_decisions;
  UPDATE_AVERAGE (averages.current.decisions, decisions);
  saved_decisions = current;
}

/*------------------------------------------------------------------------*/

// This is the main conflict analysis routine.  It assumes that a conflict
// was found.  Then we derive the 1st UIP clause, optionally minimize it,
// add it as learned clause, and then uses the clause for conflict directed
// back-jumping and flipping the 1st UIP literal.  In combination with
// chronological backtracking (see discussion above) the algorithm becomes
// slightly more involved.

void Internal::analyze () { //Find : analyze

  START (analyze);
  int uip = 0;
  if (!conflict)
  {
    // clause.clear();
    // vector<int> confilct_vector = _xorUnion->_bigEqvReason;
    // //int max_level = -1 , max_level_id = 0;
    // for (int i = 0 ; i < confilct_vector.size() ; i++)
    // {
    //   if (i == 0) clause.push_back(-confilct_vector[i]);
    //   else clause.push_back(confilct_vector[i]);
    //   // if (var(confilct_vector[i]).level > max_level)
    //   // {
    //   //   max_level = var(confilct_vector[i]).level;
    //   //   max_level_id = i;
    //   // }
    // }
    // //std::swap(confilct_vector[1], confilct_vector[max_level_id]);
    // uip = -clause[0];

    // // cout << "Union clause : ";
    // // for (int i = 0 ; i < clause.size() ; i ++)
    // // {
    // //   cout << clause[i] << ":" << var(clause[i]).level << " ";
    // // }
    // // cout << endl;
  }
  else
  {

    assert (conflict);
    assert (lrat_chain.empty ());
    assert (unit_chain.empty ());
    assert (unit_analyzed.empty ());
    assert (clause.empty ());

    //printf("do analyze\n");

    // First update moving averages of trail height at conflict.
    //
    UPDATE_AVERAGE (averages.current.trail.fast, num_assigned);
    UPDATE_AVERAGE (averages.current.trail.slow, num_assigned);
    update_decision_rate_average ();

    /*----------------------------------------------------------------------*/

    if (external_prop && !external_prop_is_lazy && opts.exteagerreasons) {
      explain_external_propagations ();
    }

    // printf("before is : "); pri_val_clause(conflict);

    if (opts.chrono || external_prop) {

      int forced;

      const int conflict_level = find_conflict_level (forced);

      // XOR conflict shortcut: when the conflict is an XOR clause with
      // multiple literals at the highest decision level, try to XOR-resolve
      // them away using their reason clauses.  This eliminates pivots and
      // often produces a single UIP, allowing us to drive directly from
      // In principle we can perform conflict analysis as in non-chronological
      // backtracking except if there is only one literal with the maximum
      // assignment level in the clause.  Then standard conflict analysis is
      // unnecessary and we can use the conflict as a driving clause.  In the
      // pseudo code of the SAT'18 paper on chronological backtracking this
      // corresponds to the situation handled in line 4-6 in Alg. 1, except
      // that the pseudo code in the paper only backtracks while we eagerly
      // assign the single literal on the highest decision level.

      if (forced) {

        assert (forced);
        assert (conflict_level > 0);
        LOG ("single highest level literal %d", forced);

        backtrack (conflict_level - 1);

        build_chain_for_units (forced, conflict, 0);

        LOG ("forcing %d", forced);
        if (conflict && conflict->xor_flag)
        {
          bool assigned = false;
          for (auto c_lit : *conflict) {
            int vc = val(c_lit);
            if (vc > 0) assigned ^= true;
            else if (c_lit == forced) assigned ^= true;
            else if (c_lit == -forced) assigned ^= false;
          }
          if (assigned) search_assign_driving (forced, conflict);
          else search_assign_driving (-forced, conflict);
        }
        else if (conflict && conflict->mixed_flag)
        {
          // For mixed clauses: the forced literal must make its block SAT.
          // All other blocks are falsified (even parity, fully assigned at
          // lower levels).  Find which block contains 'forced', compute
          // parity of other literals in that block, and assign accordingly.
          // Odd other parity → force FALSE; Even other parity → force TRUE.
          const int *offsets = conflict->block_offsets ();
          int nb = conflict->mixed_num_blocks;
          bool other_parity = false;
          for (int bi = 0; bi < nb; bi++) {
            int bs = (bi == 0) ? 0 : offsets[bi - 1];
            int be = offsets[bi];
            bool in_block = false;
            for (int j = bs; j < be; j++) {
              if (abs (conflict->literals[j]) == abs (forced))
                { in_block = true; break; }
            }
            if (in_block) {
              for (int j = bs; j < be; j++) {
                if (abs (conflict->literals[j]) == abs (forced)) continue;
                if (val (conflict->literals[j]) > 0) other_parity = !other_parity;
              }
              break;
            }
          }
          if (other_parity) // odd parity → force FALSE
            search_assign_driving (-forced, conflict);
          else // even parity → force TRUE
            search_assign_driving (forced, conflict);
        }
        else search_assign_driving (forced, conflict);

        conflict = 0;
        if (!opts.chrono)
          did_external_prop = true;
        STOP (analyze);
        return;
      }

      // Backtracking to the conflict level is in the pseudo code in the
      // SAT'18 chronological backtracking paper, but not in their actual
      // implementation.  In principle we do not need to backtrack here.
      // However, as a side effect of backtracking to the conflict level we
      // set 'level' to the conflict level which then allows us to reuse the
      // old 'analyze' code as is.  The alternative (which we also tried but
      // then abandoned) is to use 'conflict_level' instead of 'level' in the
      // analysis, which however requires to pass it to the 'analyze_reason'
      // and 'analyze_literal' functions.
      //
      //printf("backtracking 2\n");
      backtrack (conflict_level);
    }

    // Actual conflict on root level, thus formula unsatisfiable.
    //
    if (!level) {
      learn_empty_clause ();
      if (external->learner)
        external->export_learned_empty_clause ();
      STOP (analyze);
      return;
    }

    /*----------------------------------------------------------------------*/

    // First derive the 1st UIP clause by going over literals assigned on the
    // current decision level.  Literals in the conflict are marked as 'seen'
    // as well as all literals in reason clauses of already 'seen' literals on
    // the current decision level.  Thus the outer loop starts with the
    // conflict clause as 'reason' and then uses the 'reason' of the next
    // seen literal on the trail assigned on the current decision level.
    // During this process maintain the number 'open' of seen literals on the
    // current decision level with not yet processed 'reason'.  As soon 'open'
    // drops to one, we have found the first unique implication point.  This
    // is sound because the topological order in which literals are processed
    // follows the assignment order and a more complex algorithm to find
    // articulation points is not necessary.
    //
    Clause *reason = conflict;
    LOG (reason, "analyzing conflict");

    assert (clause.empty ());
    assert (lrat_chain.empty ());

    // XOR conflict: bump all variables in the XOR clause
    if (conflict->xor_flag) {
      for (auto lit : *conflict)
        bump_variable (lit);
    }

    const auto &t = &trail;
    int i = t->size ();      // Start at end-of-trail.
    int open = 0;            // Seen but not processed on this level.
    uip = 0;             // The first UIP literal.
    int resolvent_size = 0;  // without the uip
    int antecedent_size = 1; // with the uip and without unit literals
    int conflict_size = 0;   // without the uip and without unit literals
    int resolved = 0;        // number of resolution (0 = clause in CNF)
    int for_cnt = 0;
    const bool otfs = false;  // disabled: incompatible with XOR clause signs

    for (;;) {
      for_cnt ++;
      //printf("uip start,cnt is %d\n",for_cnt);
      antecedent_size = 1; // for uip

      // reason->pri_clause();
      // if (reason->literals[0] == -138 && reason->literals[1] == -24)
      // {
      //   printf("debug_now\n");
      // }
      //pri_val_clause(reason);
      //printf("analyze by 1\n");
      analyze_reason (uip, reason, open, resolvent_size, antecedent_size);
      //printf("uip mid end\n");
      if (resolved == 0)
        conflict_size = antecedent_size - 1;
      assert (resolvent_size == open + (int) clause.size ());

      //printf("if forward : ");reason->pri_clause();
      if (otfs && resolved > 0 && antecedent_size > 2 &&
          resolvent_size < antecedent_size) {
        assert (reason != conflict);
        LOG (analyzed, "found candidate for OTFS conflict");
        LOG (clause, "found candidate for OTFS conflict");
        LOG (reason, "found candidate (size %d) for OTFS resolvent",
            antecedent_size);
      
        int other;
        if (reason -> xor_flag)
        {
          if (abs(reason->literals[0]) == abs(uip))
          {
            other = reason->literals[1];
          }
          else other = reason->literals[0];
        }
        else other = reason->literals[0] ^ reason->literals[1] ^ uip;
        
        //printf("?? other : %d , 0 : %d , 1 : %d,uip:%d\n",other,reason->literals[0],reason->literals[1],uip);
        // reason = on_the_fly_strengthen (reason, uip);
        //printf("other is %d,reason is : ",other); reason->pri_clause();
        assert (other != uip);
        // if (opts.bump)
        //   bump_variables ();

        //printf("on the fly end\n");
        assert (conflict_size);
        if (!reason) {
          uip = -other;
          assert (open == 1);
          LOG ("clause is actually unit %d, stopping", -uip);
          reverse (begin (mini_chain), end (mini_chain));
          for (auto id : mini_chain)
            lrat_chain.push_back (id);
          mini_chain.clear ();
          clear_analyzed_levels ();
          assert (!opts.exteagerreasons);
          clause.clear ();
          break;
        }
        assert (conflict_size >= 2);

        //printf("lrat_chain end\n");

        if (resolved == 1 && resolvent_size < conflict_size) {
          // here both clauses are part of the CNF, so one subsumes the other
          otfs_subsume_clause (reason, conflict);
          LOG (reason, "changing conflict to");
          --conflict_size;
          assert (conflict_size == reason->size);
          ++stats.otfs.subsumed;
          ++stats.subsumed;
        }

        LOG (reason, "changing conflict to");
        conflict = reason;
        //printf("conflict is by reason: "); conflict->pri_clause();
        //printf("why now? open is %d\n",open);
        if (open == 1) {
          int forced = 0;
          const int conflict_level = otfs_find_backtrack_level (forced);
          int new_level = determine_actual_backtrack_level (conflict_level);
          UPDATE_AVERAGE (averages.current.level, new_level);
          // printf("backtracking 3\n");
          backtrack (new_level);

          LOG ("forcing %d", forced);
          search_assign_driving (forced, conflict);

          // Clean up.
          //
          conflict = 0;
          clear_analyzed_literals ();
          clear_analyzed_levels ();
          clause.clear ();
          STOP (analyze);
          return;
        }

        stats.conflicts++;

        clear_analyzed_literals ();
        clear_analyzed_levels ();
        clause.clear ();
        resolvent_size = 0;
        antecedent_size = 1;
        resolved = 0;
        open = 0;
        //printf("analyze by 2\n");
        //pri_val_clause(reason);
        analyze_reason (0, reason, open, resolvent_size, antecedent_size);
        conflict_size = antecedent_size - 1;
        assert (open > 1);
      }

      //printf("uip end\n");
      ++resolved;

      uip = 0;
      while (!uip) {
        if (!i) {
          //printf("uip is running\n");
          lazy_external_propagator_out_of_order_clause (uip);
          if (unsat)
            return;
          else if (uip) {
            open = 1;
            break;
          } else {
            LOG (reason, "restarting the analysis on the new conflict");
            ++stats.conflicts;
            reason = conflict;
            resolvent_size = 0;
            antecedent_size = 1;
            resolved = 0;
            open = 0;
            //printf("analyze by 3\n");
            analyze_reason (0, reason, open, resolvent_size, antecedent_size);
            conflict_size = antecedent_size - 1;
            assert (open > 1);
          }
        }
        assert (i > 0);
        const int lit = (*t)[--i];
        if (!flags (lit).seen)
          continue;
        if (var (lit).level == level)
          uip = lit;
      }
      if (!--open)
        break;
      reason = var (uip).reason;
      //printf("uip is %d\n",uip);
      //if (xor_con_size) xor_conflict_clause[xor_con_size]->pri_clause("xor_con");
      //if (xor_con_size) printf("xor_con : ") , pri_val_clause(xor_conflict_clause[xor_con_size]);
      //if (reason) reason->pri_clause("reason");
      if (reason == external_reason) {
        assert (!opts.exteagerreasons);
        reason = learn_external_reason_clause (-uip, 0, true);
        var (uip).reason = reason;
      }
      if (!reason) {
        LOG ("reason for UIP %d is NULL, treating as decision variable", uip);
      }
      assert (reason != external_reason);
      LOG (reason, "analyzing %d reason", uip);
      assert (resolvent_size);
      --resolvent_size;
    }

    // printf("analyze finish\n");
  LOG ("first UIP %d", uip);
  // printf("uip is %d\n",uip);
  clause.push_back (-uip);

    // Optional XOR-aware UIP replacement:
    // only on pure XOR reason cones, with strict structural checks.
    if (opts.xoruip && clause.size () > 1) {
      std::vector<int> baseline_clause = clause;
      std::vector<int> xor_uip_clause;
      if (try_xor_uip_clause (uip, baseline_clause, xor_uip_clause)) {
        // Additional safety gate: never worsen clause size in this mode.
        if (xor_uip_clause.size () <= baseline_clause.size ())
          clause.swap (xor_uip_clause);
      }
    }
  }

  // Update glue and learned (1st UIP literals) statistics.
  //
  int size = (int) clause.size ();
  const int glue = (int) levels.size () - 1;
  LOG (clause, "1st UIP size %d and glue %d clause", size, glue);
  UPDATE_AVERAGE (averages.current.glue.fast, glue);
  UPDATE_AVERAGE (averages.current.glue.slow, glue);
  stats.learned.literals += size;
  stats.learned.clauses++;
  assert (glue < size);

  // up to this point lrat_chain contains the proof for current clause in
  // reversed order. in minimize and shrink the clause is changed and
  // therefore lrat_chain has to be extended. Unfortunately we cannot create
  // the chain directly during minimization (or shrinking) but afterwards we
  // can calculate it pretty easily and even better the same algorithm works
  // for both shrinking and minimization.

  // Minimize the 1st UIP clause as pioneered by Niklas Soerensson in
  // MiniSAT and described in our joint SAT'09 paper.
  //
  if (size > 1) {
    // Re-enabled: analyze_reason() now uses flipped copies instead of
    // in-place mutation, making recursive minimization safe for XOR clauses.
    if (opts.minimize)
      minimize_clause ();

    size = (int) clause.size ();

    // Update decision heuristics.
    //
    // if (opts.bump) {
    //   bump_also_all_reason_literals ();
    //   bump_variables ();
    // }

    if (external->learner)
      external->export_learned_large_clause (clause);
  } else if (external->learner)
    external->export_learned_unit_clause (-uip);

  // Update actual size statistics.
  //
  stats.units += (size == 1);
  stats.binaries += (size == 2);
  UPDATE_AVERAGE (averages.current.size, size);

  // reverse lrat_chain. We could probably work with reversed iterators
  // (views) to be more efficient but we would have to distinguish in proof
  //
  if (lrat) {
    LOG (unit_chain, "unit chain: ");
    for (auto id : unit_chain)
      lrat_chain.push_back (id);
    unit_chain.clear ();
    reverse (lrat_chain.begin (), lrat_chain.end ());
  }

  // Determine back-jump level, learn driving clause, backtrack and assign
  // flipped 1st UIP literal.
  //

  // cout << "clasue : ";
  // for (auto it : clause)
  // {
  //   cout << it << " : " << var(it).level << endl;
  // }


  int jump;
  Clause *driving_clause = new_driving_clause (glue, jump);
  UPDATE_AVERAGE (averages.current.jump, jump);

  // driving_clause->pri_clause("driving_clause");

  int new_level = determine_actual_backtrack_level (jump);
  UPDATE_AVERAGE (averages.current.level, new_level);
  //printf("backtracking 4\n");
  backtrack (new_level);

  // It should hold that (!level <=> size == 1)
  //                 and (!uip   <=> size == 0)
  // this means either we have already learned a clause => size >= 2
  // in this case we will not learn empty clause or unit here
  // or we haven't actually learned a clause in new_driving_clause
  // then lrat_chain is still valid and we will learn a unit or empty clause
  //
  if (uip) {
    search_assign_driving (-uip, driving_clause);
  } else
    learn_empty_clause ();

  // printf("learn clause: " );
  // if (driving_clause) driving_clause->pri_clause();

  if (stable)
    reluctant.tick (); // Reluctant has its own 'conflict' counter.

  // Clean up.
  //
  clear_analyzed_literals ();
  clear_unit_analyzed_literals ();
  clear_analyzed_levels ();
  clause.clear ();
  conflict = 0;

  lrat_chain.clear ();
  STOP (analyze);

  if (driving_clause && opts.eagersubsume)
    eagerly_subsume_recently_learned_clauses (driving_clause);

  if (lim.recompute_tier <= stats.conflicts)
    recompute_tier ();
}

// In the special case where the external propagator is lazy, the same
// invariants as OTFS break (but even more complicated). There are three
// possible cases:
//   - the clause becomes empty (unsat must be answered)
//   - the clause is a unit (backtrack and set the clause)
//   - the clause is a new conflict on lower level and we restart the
//   analysis
//
// TODO: we do not really need to keep the clause longer than the conflict
// analysis.
void Internal::lazy_external_propagator_out_of_order_clause (int &uip) {
  assert (!opts.exteagerreasons);
  assert (external_prop);
  LOG (clause, "out-of-order conflict");
  if (clause.empty ()) {
    LOG (lrat_chain, "lrat_chain:");
    LOG (clause, "clause:");
    LOG (unit_chain, "units:");
    if (lrat) {
      LOG (unit_chain, "unit chain: ");
      for (auto id : unit_chain)
        lrat_chain.push_back (id);
      unit_chain.clear ();
      reverse (lrat_chain.begin (), lrat_chain.end ());
    }
    LOG (lrat_chain, "lrat_chain:");
    learn_empty_clause ();
    if (external->learner)
      external->export_learned_empty_clause ();
    conflict = 0;
  } else if (clause.size () == 1) {
    LOG ("found out-of-order unit");
    uip = -clause[0];
    assert (uip);
    //printf("backtracking 5\n");
    backtrack (var (uip).level);
    assert (val (uip) > 0);
    clause.clear ();
  } else {
    int jump;
    const int glue = clause.size () - 1;
    conflict = new_driving_clause (glue, jump);
    UPDATE_AVERAGE (averages.current.level, jump);
    //printf("backtracking 6\n");
    backtrack (jump);
    LOG (conflict, "new conflict");
  }
  // Clean up.
  //
  clear_analyzed_literals ();
  clear_unit_analyzed_literals ();
  clear_analyzed_levels ();
  clause.clear ();

  if (unsat) {
    lrat_chain.clear ();
    STOP (analyze);
  }
}

// We wait reporting a learned unit until propagation of that unit is
// completed.  Otherwise the 'i' report gives the number of remaining
// variables before propagating the unit (and hides the actual remaining
// variables after propagating it).

void Internal::iterate () {
  iterating = false;
  report ('i');
}

} // namespace CaDiCaL
