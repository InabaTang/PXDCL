#include "union.hpp"

namespace CaDiCaL {

UnionSet::UnionSet (Internal *i)
    : inter (i)
{
    assert (inter);
    assert (!inter->external);
    inter->_xorUnion = this;
}

void UnionSet::AllocateMemory(int max_var)
{
    if (_maxvar == max_var) return ;
    
    _maxvar = max_var;
    _father = new int [(_maxvar + 5) << 1];
    _queryRoot = new int [(_maxvar + 5) << 1];
    _litStamp = new unsigned[(_maxvar + 5) << 1];

    _trail      = new int [(_maxvar + 5) << 1];
    _treeRank   = new unsigned[(_maxvar + 5) << 1];
    _litDepth   = new unsigned[(_maxvar + 5) << 1];
    _rankPlus   = new bool    [(_maxvar + 5) << 1];
    _reasonStamp = new unsigned[(_maxvar + 5) << 1];
    _reasonPos = new int [(_maxvar + 5) << 1];
    _reasonStampTick = 1;

    _lv2Trail   = new unsigned [(_maxvar + 5) << 1];

    _varReasons = new vector<int> [_maxvar + 5];

    _bigEqvReason.clear();

    _levelSize = _trailSize = 0;
    _timeStamp = _backStamp = 0;

    //for var = 0
    _queryRoot[0] = 0;
    _father[0] = 0;
    _litStamp[0] = 0;
    _litDepth[0] = 0;
    _treeRank[0] = 1;
    _rankPlus[0] = false;

    for (int var = 1 ; var <= _maxvar; var++)
    {
        int lit = inter->vlit(var);
        int flit = inter->vlit(-var);
        _queryRoot[lit] = _father[lit] = lit;
        _queryRoot[flit] = _father[flit] = flit;
        _litStamp[lit] = _litStamp[flit] = 0;
        _reasonStamp[lit] = _reasonStamp[flit] = 0;
        _reasonPos[lit] = _reasonPos[flit] = -1;

        _treeRank[lit] = _treeRank[flit] = 1;
        _litDepth[lit] = _litDepth[flit] = 0;
        _rankPlus[lit] = _rankPlus[flit] = false;
    }
    
}

void UnionSet::ExtendLevel() 
{
    _lv2Trail[_levelSize] = _trailSize;
    _levelSize++;
}

void UnionSet::BackJump(unsigned backLevel) {
    _levelSize = backLevel;
    _backStamp ++;

    int lit;
    while (_trailSize > _lv2Trail[_levelSize]) {
        lit = _trail[--_trailSize];
        int v_lit = inter->vlit(lit);

        if (_rankPlus[v_lit]) {
            _treeRank[_father[v_lit]]--;
            _rankPlus[v_lit] = false;
        }

        _litDepth[v_lit]   = 0;
        _queryRoot[v_lit]  = v_lit; 
        _father[v_lit]     = v_lit;
    }
}

bool UnionSet::Union(int lit1, int lit2, int reason) {
    //cout << "Union " << lit1 << ' ' << lit2 << std::endl;
    int rt1 = Find(lit1);
    int rt2 = Find(lit2);

    int lit_rt1 = inter->slit(rt1);
    int lit_rt2 = inter->slit(rt2);

    //cout << "Union2 " << lit_rt1 << ' ' << lit_rt2 << std::endl;

    int frt1 = inter->vlit(-lit_rt1);
    int frt2 = inter->vlit(-lit_rt2);

    // cout << "rt : " << rt1 << ' ' << rt2 << " ||| lit_rt: " << 
    // lit_rt1 << ' ' << lit_rt2 << " ||| frt: " << frt1 << ' ' << frt2 << 
    // " ||| lit:" << lit1 << ' ' << lit2 << std::endl;

    if (lit_rt1 ==  lit_rt2) return true;        // already in same eqv-class
    if (lit_rt1 == -lit_rt2) return false;       // have conflict


    if (_treeRank[rt1] < _treeRank[rt2]) {
        std::swap(frt1, frt2);
        std::swap(lit_rt1, lit_rt2);

        std::swap(rt1, rt2);            // make rt1 as new root
        std::swap(lit1, lit2);
    } else if (_treeRank[rt1] == _treeRank[rt2]) {
        _treeRank[rt1] ++; _treeRank[frt1] ++;
        _rankPlus[rt2] = _rankPlus[frt2] = true; 
    }

    _bigEqvReason.clear();
    // reason==0 means a permanent/root equivalence without a trail literal.
    // Keep it out of reason vectors: literal '0' is not a valid SAT literal
    // and can corrupt learned conflict clauses.
    if (reason) _bigEqvReason.push_back(reason);
    GetReasonPath(lit_rt1, lit1);
    GetReasonPath(lit_rt2, lit2);
    StoreReasonPath(Get_Var(inter->slit(rt2)));

    AddFather(rt1, rt2);                // father[rt2] = rt1
    AddFather(frt1, frt2);
    _litDepth[rt2] = _litDepth[frt2] = 1;

    return true;
}

void UnionSet::AddFather(int rt1, int rt2) {
    // cout << "AddFather [" << ExtLit(rt2) << "] = " << ExtLit(rt1) << std::endl;
    _trail[_trailSize++] =  inter->slit(rt2);
    _father[rt2]         =  rt1;
    _queryRoot[rt2]      =  rt1;
}
int UnionSet::Havelit(int lit , vector<int> big)
{
    int size = big.size();
    for (int i = 0; i < size; i++)
    {
        if (big[i] == lit) return i;
    }
    return -1;
}

void UnionSet::Eraselit(int id , vector<int> &big)
{
    int size = big.size();
    big[id] = big[size - 1];
    big.pop_back();
}

void UnionSet::AddVarReason(int lvar) 
{
  const vector<int> &reason = _varReasons[lvar];
  if (reason.empty ()) return;

    // Build membership of current reason set in O(|_bigEqvReason|).
    if (++_reasonStampTick == 0) {
        memset (_reasonStamp, 0, sizeof(unsigned) * (((_maxvar + 5) << 1)));
        _reasonStampTick = 1;
    }
    for (size_t i = 0; i < _bigEqvReason.size (); i++) {
        const int lit = _bigEqvReason[i];
        const int idx = inter->vlit (lit);
        _reasonStamp[idx] = _reasonStampTick;
        _reasonPos[idx] = (int) i;
    }

    for (int lit : reason) {
        if (!lit) continue;
        const int idx = inter->vlit(lit);
        if (_reasonStamp[idx] == _reasonStampTick) {
            // Symmetric-difference cancellation in O(1).
            const int pos = _reasonPos[idx];
            assert (pos >= 0 && (size_t) pos < _bigEqvReason.size ());
            const int moved_lit = _bigEqvReason.back ();
            _bigEqvReason[pos] = moved_lit;
            _bigEqvReason.pop_back ();
            if ((size_t) pos < _bigEqvReason.size ()) {
                const int moved_idx = inter->vlit (moved_lit);
                _reasonPos[moved_idx] = pos;
            }
            _reasonStamp[idx] = 0;
            _reasonPos[idx] = -1;
        } else {
            _reasonPos[idx] = (int) _bigEqvReason.size ();
            _bigEqvReason.push_back (lit);
            _reasonStamp[idx] = _reasonStampTick;
        }
    }
}

int UnionSet::Find(int lit) {
    int v_lit = inter->vlit(lit);

    // queryRoot/litDepth caches are valid only for current backtrack epoch.
    if (_litStamp[v_lit] != _backStamp)
    {
        _queryRoot[v_lit] = v_lit;
        _litDepth[v_lit] = 0;
    }

    int tmpRoot;
    if (_queryRoot[v_lit] == _father[_queryRoot[v_lit]]) {  // do nothing
        assert(_litDepth[_queryRoot[v_lit]] == 0);
    } else if (_queryRoot[v_lit] == v_lit) {                // from itself
        tmpRoot         = Find(inter->slit(_father[v_lit]));
        _litDepth[v_lit]  = _litDepth[_father[v_lit]] + 1;
        _queryRoot[v_lit] = tmpRoot;
    } else {                                            // from queryRoot
        tmpRoot         = Find(inter->slit(_queryRoot[v_lit]));
        _litDepth[v_lit] += _litDepth[_queryRoot[v_lit]];   // litDept[lit] = path from lit to _queryRoot[lit]
        _queryRoot[v_lit] = tmpRoot;
    }

    _litStamp[v_lit] = _backStamp;
    return _queryRoot[v_lit];
}

void UnionSet::GetReasonPath(int lit1, int lit2) {
    int v_lit1 = inter->vlit(lit1);
    int v_lit2 = inter->vlit(lit2);
    int rt1 = Find(lit1), rt2 = Find(lit2);
    if (rt1 != rt2) {
        cout << "!!!!! " <<  lit1 << " root at " << Find(lit1) << "   and   " << lit2 << " root at " << Find(lit2) << std::endl;
        assert (Find(lit1) == Find(lit2));          // this only make sure correct litDepth on lit1 and lit2
    }
    if (_litDepth[v_lit1] > _litDepth[v_lit2])
    {
        std::swap(lit1, lit2);
        std::swap(v_lit1, v_lit2);
    }

    // cout << "GetReasonPath:  litDepth:  [" << v_lit1 << "] = " << _litDepth[v_lit1] << "    [" << inter->vlit(lit2) << "] = " << _litDepth[v_lit2] << std::endl; 

    while (_litDepth[v_lit2] != _litDepth[v_lit1]) {
        //assert(_litDepth[_father[v_lit2]] == _litDepth[v_lit2] - 1);

        _litDepth[_father[v_lit2]]  = _litDepth[v_lit2] - 1;
        _queryRoot[_father[v_lit2]] = rt2;
        AddVarReason(Get_Var(lit2));
        lit2 = inter->slit(_father[v_lit2]);
        v_lit2 = _father[v_lit2];
    }

    while (lit1 != lit2) {
        assert(Find(lit1) == Find(lit2));
        //cout << "??? GetReasonPath: " << lit1 << "  " << lit2 << std::endl;
        _litDepth[_father[v_lit1]]  = _litDepth[v_lit1] - 1;
        _queryRoot[_father[v_lit1]] = rt1;

        _litDepth[_father[v_lit2]]  = _litDepth[v_lit2] - 1;
        _queryRoot[_father[v_lit2]] = rt2;

        // if (DEBUG) assert(_litDepth[_father[lit1]] == _litDepth[lit1] - 1);
        // if (DEBUG) assert(_litDepth[_father[lit2]] == _litDepth[lit2] - 1);

        AddVarReason(Get_Var(lit1));
        lit1 = inter->slit(_father[v_lit1]);
        v_lit1 = _father[v_lit1];
        AddVarReason(Get_Var(lit2));
        lit2 = inter->slit(_father[v_lit2]);
        v_lit2 = _father[v_lit2];
    }
}

void UnionSet::StoreReasonPath(int lvar) {
    _varReasons[lvar] = _bigEqvReason;
    // cout << "Store on " << var << " reason: "; _varReasons[var].Display('#');
}

// lit1 == ~lit2 && reason == 0 -> lit1 == lit2, conflict
void UnionSet::GetConflictPath(int lit1, int lit2, int reason) {
    //cout << "! run getconflictpath" << endl;
    //cout << "GetConflictPath:  lit1 = " << lit1 << "  lit2 = " << lit2 << "  reason = " << reason << std::endl;
    //assert(inter->var(reason).level <= _levelSize);
    assert (inter->slit(Find(lit1)) == -inter->slit(Find(lit2)));
    _bigEqvReason.clear();
    if (reason) _bigEqvReason.push_back(reason);
    GetReasonPath(lit1, -lit2);
}

void UnionSet::PrintTrail() 
{
    unsigned i = 0, lv = 0;
    cout << "Union DisplayTrail LevelSize: " << _levelSize << std::endl << lv << ": ";
    while (lv <= _levelSize && i < _trailSize) {
        cout << _trail[i++] << " ";
        if (i == _lv2Trail[lv] && lv < _levelSize) {
            cout << std::endl << (++lv) << ": ";
        }
    }
    cout << std::endl;
}

void Internal::AddXorGate(Clause *xorcon) {
    if (xorcon->size == 3)
    {
        int a = xorcon->literals[0];
        int b = xorcon->literals[1];
        int c = xorcon->literals[2];

        // XOR constraint: a ⊕ b ⊕ c = 1
        // When a=TRUE:  b⊕c=0 → b=c  → equivalence b↔c
        // When a=FALSE: b⊕c=1 → b≠c  → equivalence b↔¬c
        AddEqvImpl(a,  b,  c);   // a=TRUE  → b↔c
        AddEqvImpl(-a, b, -c);   // a=FALSE → b↔¬c
        AddEqvImpl(b,  a,  c);   // b=TRUE  → a↔c
        AddEqvImpl(-b, a, -c);   // b=FALSE → a↔¬c
        AddEqvImpl(c,  a,  b);   // c=TRUE  → a↔b
        AddEqvImpl(-c, a, -b);   // c=FALSE → a↔¬b
    }
}

// a == 0 -> b == c
void Internal::AddEqvImpl(int a , int b , int c)
{
    Eqvmap & eqvMap = _eqvMaps[vlit(a)];

    if (opts.uniondebug)
    {
        if (eqvMap.count(b)) {
        cout << "AddEqvImpl: " << a << " " << b << " -> " << c << std::endl;
        cout << "Already Have: " << a << " " << b << " -> " <<  eqvMap[b] << std::endl;
        return ;
        } else if (eqvMap.count(-b)) {
            cout << "AddEqvImpl: " << a << " " << b << " -> " << c << std::endl;
            cout << "Already Have: " << a << " " << -b << " -> " <<  eqvMap[-b] << std::endl;
            return ;
        }
        assert(eqvMap.find(b) == eqvMap.end());
        assert(eqvMap.find(-b) == eqvMap.end());
    }

    else
    {
        if (eqvMap.count(b) || eqvMap.count(-b)) return ; 
    }

    eqvMap[b] = c;
    eqvMap[c] = b;
}

void Internal::AddEqvRelation(int lit1 , int lit2 , int reason)
{
    if (lit1 == lit2) return;

    // Canonicalize key so (a,b)==(b,a) and (a,b)==(-a,-b).
    int a = lit1, b = lit2;
    if (a > b) std::swap(a, b);
    int na = -a, nb = -b;
    if (na > nb) std::swap(na, nb);
    if (na < a || (na == a && nb < b)) {
        a = na;
        b = nb;
    }
    const uint64_t key =
        (uint64_t)(uint32_t)a << 32 | (uint32_t)b;

    // Skip duplicate queued relations in current search state.
    if (_eqv_relation_hash.find(key) != _eqv_relation_hash.end()) return;

    if (_xorUnion->JudgeEqv(lit1, lit2)) return ;

    _eqvRelations[_eqvRelationSize] = make_pair(lit1, lit2);
    _eqvReasons[_eqvRelationSize] = reason;
    _eqv_relation_keys.push_back(key);
    _eqv_relation_hash.insert(key);
    _eqvRelationSize ++;
}

vector<int> Internal::EqvPropagation(unsigned start)
{
    vector<int> ret;
    ret.clear();
    // Propagate equivalence relations to a fixed point for this batch:
    // newly added relations can imply further merges in the same call.
    while (start < (unsigned) _eqvRelationSize) {
        const unsigned end = _eqvRelationSize;
        for (; start < end; start++) {
            std::pair<int, int> &relation = _eqvRelations[start];

            if (_xorUnion->JudgeEqv(relation.first, relation.second)) continue;

            if (!_xorUnion->Union(relation.first, relation.second,
                                  _eqvReasons[start])) {
                _xorUnion->GetConflictPath(relation.first, relation.second,
                                           _eqvReasons[start]);
                return _xorUnion->_bigEqvReason;
            }
        }
    }

    return ret;
}


void Internal::make_vector_to_xor_confilct(int lvar, vector<int> clause)
{
    const int size = (int) clause.size ();
    int glue = size;
    const size_t header_bytes = sizeof (Clause);
    const size_t actual_literal_bytes = size * sizeof (int);
    size_t combined_bytes = header_bytes + actual_literal_bytes;
    size_t aligned_bytes = align (combined_bytes, alignof (Clause *));
    size_t bytes = aligned_bytes;
    Clause *c = (Clause *) new char[bytes];
    DeferDeleteArray<char> clause_delete ((char *) c);

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
    c->redundant = false;
    c->transred = false;
    c->subsume = false;
    c->swept = false;
    c->flushed = false;
    c->vivified = false;
    c->vivify = false;
    c->used = 0;
    c->xor_flag = false;
    c->xor_conflict_flag = true;

    c->glue = glue;
    c->size = size;
    c->pos = 2;

    for (int i = 0; i < size; i++)
    {
        //if (c->xor_flag) printf("%d : %d \n",i,clause[i]);
        c->literals[i] = clause[i];
    }

    mark_added(c);

    xor_conflict_clause = c;

    return ;
}

void UnionSet::Display(vector<int>v)
{
    int sz = v.size();
    for (int i = 0 ; i < sz ; i ++)
    {
        cout << v[i] << " ";
    }
    cout << endl;
}


}
