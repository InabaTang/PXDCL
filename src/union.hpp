#ifndef _union_hpp_INCLUDED
#define _union_hpp_INCLUDED

#include "internal.hpp"
#include <vector>

namespace CaDiCaL {

using std::vector;
struct Clause;
struct Internal;

class UnionSet
{
public:
    int _maxvar;

    unsigned  _timeStamp;
    unsigned  _backStamp;

    unsigned  *_litStamp;
    int   *_father;     // build union set tree [lit]
    int   *_queryRoot;  // query root, path compression [lit]

    unsigned  *_treeRank;   // subtree rank (tree depth) [lit]
    bool      *_rankPlus;   // true - add father rank by add [lit]
    unsigned  *_litDepth;   // litDepth in union set tree (to queryRoot) [lit]

    int   *_trail; // union trail, for backTrack [var]
    unsigned   _trailSize;

    unsigned  *_lv2Trail;
    unsigned   _levelSize;  // <= _maxVar

    UnionSet(){};
    UnionSet(Internal *inter);

    vector<int> *_varReasons;
    vector<int> _bigEqvReason;
    Internal *inter;
    void AllocateMemory(int max_var);
    void FreeMemory();

    void ExtendLevel();
    void BackJump(unsigned backLevel);
    bool Union(int lit1, int Lit2, int reason);
    void AddFather(int lit1, int lit2);

    int Find(int lit);
    bool JudgeEqv(int lit1, int lit2) { return Find(lit1) == Find(lit2); }
    int Get_Var(int lit) { if (lit < 0) return -lit; else return lit; }

    void    AddVarReason(int var);
    void    GetReasonPath(int lit1, int lit2);    // add reason path to _bigEqvReason
    void    StoreReasonPath(int var);
    void    GetConflictPath(int lit1, int lit2, int reason);

    void PrintTrail();
    int Havelit(int lit , std::vector<int> big);
    void Eraselit(int id , vector<int> &big);
    void Display(vector<int>v);

    Clause *vector2clause(vector<int> big);
};

}


#endif