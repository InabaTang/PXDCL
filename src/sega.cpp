#include "sega.hpp"

namespace CaDiCaL {

bool Internal::segaing()
{
    return !xor_full_clause.empty();
}

// Process fully-assigned long XOR clauses (size > 5).
// Uses incrementally-tracked xor_clause_parity (no recomputation needed).
// If violated, set conflict = clause (analyze() handles xor_flag).
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

        // Use incrementally-tracked parity: odd number of true = satisfied
        if (xor_clause_parity[ci])
            continue;  // satisfied

        // XOR violated: all literals assigned false (even parity).
        // Use the XOR clause directly as conflict — analyze() at
        // analyze.cpp:327 handles xor_flag clauses by flipping true
        // literals to false before resolving.
        conflict = c;
        printf("c SEGA conflict from long XOR clause, size %d (ci %d)\n",
               c->size, ci);
        break;
    }
}

} // namespace CaDiCaL
