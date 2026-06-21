#ifndef _gauss_hpp_INCLUDED
#define _gauss_hpp_INCLUDED
#include "internal.hpp"
#include "m4ri/m4ri.h"

namespace CaDiCaL {

struct XorLine
{
    int l , r , id;
    XorLine (int l, int r , int id) : l (l), r (r), id (id){}
    XorLine () {}

    bool operator < (const XorLine & x) const
    {
        return r < x.r;
    }
};

struct SegmentTree {
    #define lson node << 1
    #define rson node << 1 | 1

    struct node {
        int lazy, maxn, pos;
    };
    vector<node> s;

    SegmentTree (int n) {
        s.resize(4 * n + 5);
    }

    void spread(int node) {
        if(s[node].lazy) {
            s[lson].lazy += s[node].lazy;
            s[rson].lazy += s[node].lazy;
            s[lson].maxn += s[node].lazy;
            s[rson].maxn += s[node].lazy;
            s[node].lazy = 0;
        }
    }

    void pushup(int node) {
        if (s[lson].maxn >= s[rson].maxn) {
            s[node].maxn = s[lson].maxn;
            s[node].pos = s[lson].pos;
        } else {
            s[node].maxn = s[rson].maxn;
            s[node].pos = s[rson].pos;
        }
    }

    void build(int node, int l, int r, int* ar) {
        s[node].lazy = 0;
        if (l == r) {
            s[node].maxn = ar[l];
            s[node].pos = l;
            return;
        }
        int mid = (l+r)>>1;
        build(lson, l, mid, ar);
        build(rson, mid+1, r, ar);
        pushup(node);
    }
    
    void change(int node, int l, int r, int L, int R, int val) {
        if (L <= l && r <= R) {
            s[node].maxn += val;
            s[node].lazy += val;
            return;
        }
        spread(node);
        int mid = (l+r)>>1;
        if (L <= mid) change(lson, l, mid, L, R, val);
        if (R > mid) change(rson, mid+1, r, L, R, val);
        pushup(node);
    }

    pair<int,int> query(int node, int l, int r, int L, int R) {
        if (L > R) return {-1e9,0};
        if (L <= l && r <= R) return {s[node].maxn, s[node].pos};
        spread(node);
        int mid = (l+r)>>1;
        if (R <= mid) return query(lson, l, mid, L, R);
        if (L > mid) return query(rson, mid+1, r, L, R);
        auto left = query(lson, l, mid, L, mid);
        auto right = query(rson, mid+1, r, mid+1, R);
        return left.first >= right.first ? left : right;
    }
};


struct Gauss_line_xs
{
    int x;
    int flag; //0 for left , 1 for right
    int id; //id of the line

    Gauss_line_xs (int x, int flag, int id) : x (x), flag (flag), id (id) {}
    Gauss_line_xs () {}

    bool operator < (const Gauss_line_xs & ts) const
    {
        if (x == ts.x)
        {
            if (flag == ts.flag)
                return id < ts.id;
            else return flag < ts.flag;
        }
        else return x < ts.x;
    }
};

}



#endif