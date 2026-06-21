#include "gauss.hpp"

namespace CaDiCaL {

int Internal::gauss_check(int mid)
{
    gauss_dp[0][0] = 0;
    line_xs_id --;
    for (int i = 1 ; i <= line_xs_id ; i ++) gauss_dp[0][i] = -1e9;
    for (int j = 1 ; j <= block_number ; j ++)
    {
        for (int i = 0 ; i <= line_xs_id ; i ++)
        {
            segment_init[i] = gauss_dp[j - 1][i];
            gauss_dp[j][i] = -1e9;
        }
        int le = 0;
        gauss_segment->build(1 , 0 , line_xs_id, segment_init);
        int line_id = 0 , b_id = 0;
        for (int p = 1 ; p <= line_xs_id ; p ++)
        {
            if (b_id < p) b_id = p;
            while(line_xs[p].x - line_xs[le].x > mid)
            {
                le ++;
            }

            while (line_xs[b_id].x == line_xs[p].x)
            {
                if (line_xs[b_id].flag == 1)
                {
                    int l_id = line_xs_left[line_xs[b_id].id];
                    gauss_segment->change(1, 0, line_xs_id, l_id, line_xs_id, -1);
                }
                b_id ++;
            }
            pair<int,int> gauss_p = gauss_segment->query(1, 0, line_xs_id, le , p - 1);
            gauss_dp[j][p] = gauss_A[p] + gauss_p.first;
            gauss_pre[j][p] = gauss_p.second;
            //cout << "p : " << p << " " << gauss_dp[j][p] << " " << gauss_A[p] << " " << gauss_segment->querymaxn(1, 0, line_xs_id, le , p - 1) << endl;
        }
    }
    //cout << "mid : " << mid << " " << gauss_dp[block_number][line_xs_id] << endl;
    return gauss_dp[block_number][line_xs_id];
}


void Internal::gauss_division_preprocessing(int L)
{
    int bn = block_number + 10;
    for (int i = 0 ; i < bn ; i ++)
    {
        xor_kdd[i].clear();
    }
    // cout << "L = " << L << ' ' << xor_clauses.size() << endl;
    // for (int i = 0; i < gauss_division_v.size(); i++)
    // {
    //     cout << "scc_id : " << i << ' ' << gauss_division_v[i] << endl;
    // }

    for (int i = 0 ; i < xor_clauses.size(); i ++)
    {
        int l = xor_lines[i].l;
        int r = xor_lines[i].r;
        int id = xor_lines[i].id;
        // cout << "??? " << l << " " << r << endl;
        // xor_clauses[id]->pri_clause();
        auto pos_l = std::lower_bound(gauss_division_v.begin() , gauss_division_v.end() , l) - gauss_division_v.begin();
        auto pos_r = std::lower_bound(gauss_division_v.begin() , gauss_division_v.end() , r) - gauss_division_v.begin();
        // for (auto it : gauss_division_v)
        // {
        //     cout << it << ' ';
        // }
        // cout << endl;
        if (pos_l == pos_r)
        {
            xor_kdd[pos_l - 1].push_back(id);
        }
        else continue;
    }

    // for (int i = 0 ; i < block_number ; i ++)
    // {
    //     cout << "scc " << i << " : ";
    //     for (auto j : xor_kdd[i])
    //     {
    //         cout << j << " ";
    //     }
    //     cout << endl;
    // }
}

void Internal::make_gauss_vector()
{
    gauss_division_v.clear();
    gauss_division_v.push_back(max_var);
    int k = 0;
    for (int i = line_xs_id ; i > 0 ; )
    {
        int t = gauss_pre[block_number - k][i];
        int le = line_xs[t].x;
        //cout << "i = " << i << ' ' << le << ' ' << t << endl;
        gauss_division_v.push_back(le);
        i = t;
        k ++;
    }
    sort(gauss_division_v.begin(), gauss_division_v.end());
    return ;
}


int Internal::gauss_division()
{
    int sz = xor_clauses.size();
    line_xs = new Gauss_line_xs[2 * sz + 1000];
    line_xs_left = new int [sz + 1000];
    block_number = min(5 , max_var / 500000 + 10);
    gauss_division_v.reserve(2 * sz + 1000);

    for (int i = 0 ; i < sz ; i ++)
    {
        Clause *c = xor_clauses[i];
        int line_l = 1e9 , line_r = -1e9;
        for (int i = 0 ; i < c->size ; i ++)
        {
            int lit = c->literals[i];
            line_l = min(line_l, abs(lit));
            line_r = max(line_r, abs(lit));
        }
        xor_lines.push_back(XorLine(line_l, line_r , i));
    }
    sort(xor_lines.begin(), xor_lines.end());

    line_xs_id = 0;
    line_xs[line_xs_id ++] = Gauss_line_xs(0 , -1 , -1);
    for (int i = 0 ; i < xor_lines.size() ; i ++)
    {
        line_xs[line_xs_id ++] = Gauss_line_xs(xor_lines[i].l, 0 , i);
        line_xs[line_xs_id ++] = Gauss_line_xs(xor_lines[i].r, 1 , i);
    }
    line_xs[line_xs_id ++] = Gauss_line_xs(max_var , -1 , -1);
    sort(line_xs , line_xs + line_xs_id);

    const int bn = block_number + 50;
    const int line_xd = line_xs_id + 50;
    gauss_dp = new int *[bn];
    gauss_pre = new int *[bn];
    for (int i = 0 ; i < bn; i ++)
    {
        gauss_dp[i] = new int[line_xd];
        gauss_pre[i] = new int[line_xd];
    }

    segment_init = new int [line_xd + 50];
    gauss_segment = new SegmentTree(line_xd + 50);

    for (int i = 0 ; i < line_xs_id ; i ++)
    {
        if (line_xs[i].flag == 0)
        {
            line_xs_left[line_xs[i].id] = i;
        }
    }

    int all_line = 0 , now_id = 0;
    for (int i = 0 ; i < line_xs_id ; i ++)
    {
        while (now_id < line_xs_id and line_xs[now_id].x <= line_xs[i].x)
        {
            if (line_xs[now_id].flag == 1) all_line ++;
            now_id ++;
        }
        gauss_A.push_back(all_line);
    }

    //for (int i = 0 ; i < line_xs_id ; i ++) cout << "i : " << i << ' ' << gauss_A[i] << endl;

    int l = 0 , r = max_var, max_clause = 0 , ans = 0;
    while(l < r)
    {
        int mid = (l + r) / 2;
        int gauss_clause = gauss_check(mid);
        if (gauss_clause > sz / 4 or gauss_clause > max_clause)
        {
            max_clause = gauss_clause;
            ans = mid;
            r = mid;
            make_gauss_vector();
        }
        else
        {
            l = mid + 1;
        }
    }
    return ans;
}

int Internal::gauss_elimination()
{
    cout << "c Gauss elimination start : " << clause_id << endl;
    for (int ca = 0 ; ca < block_number - 1; ca ++)
    {
        if (xor_kdd[ca].size() == 0) continue;
        int now_metis = gauss_division_v[ca];
        int upper_metis = gauss_division_v[ca + 1];
        int cols = upper_metis - now_metis + 1;
        int rows = xor_kdd[ca].size();
        mzd_t* mat = mzd_init(rows, cols);
        if (!mat) 
        {
            std::cerr << "Failed to allocate matrix of size " << rows << "x" << cols << std::endl;
            return true;
        }
        for (int row = 0 ; row < rows; row++)
        {
            Clause *c = xor_clauses[xor_kdd[ca][row]];
            for (int i = 0 ; i < c->size; i ++)
            {
                int lit = c->literals[i];
                assert(abs(lit) >= now_metis);
                assert(abs(lit) <= upper_metis);
                mzd_write_bit(mat, row, abs(lit) - now_metis - 1, 1);
                assert(abs(lit) - now_metis - 1 >= 0);
            }
            mzd_write_bit(mat, row, cols - 1, 1);
        }
        // printf("Matrix %dx%d:\n", mat->nrows, mat->ncols);
        // for (int row = 0; row < mat->nrows; row++) {
        //     for (int col = 0; col < mat->ncols; col++) {
        //         printf("%d ", mzd_read_bit(mat, row, col));
        //     }
        //     printf("\n");
        // }
        mzd_echelonize(mat, true);

        // printf("End Matrix %dx%d:\n", mat->nrows, mat->ncols);
        // for (int row = 0; row < mat->nrows; row++) {
        //     for (int col = 0; col < mat->ncols; col++) {
        //         printf("%d ", mzd_read_bit(mat, row, col));
        //     }
        //     printf("\n");
        // }
        for (int row = 0 , rhs ; row < xor_kdd[ca].size(); row ++)
        {
            vector<int> ones;
            int64_t id;
            for (int col = 0; col < cols - 1; col ++)
            {
                if (mzd_read_bit(mat, row, col))
                {
                    assert(mat != nullptr);
                    assert(row >= 0 && row < mat->nrows);
                    assert(col >= 0 && col < mat->ncols);
                    if (ones.size() == 2) goto NextRow;
                    ones.push_back(col + 1 + now_metis);
                }
            }

            rhs = mzd_read_bit(mat, row, cols - 1);

            original.clear();
            if (ones.size() == 1)
            {
                original.push_back(ones[0] * (rhs ? 1 : -1));
            }
            else if (ones.size() == 2)
            {
                int p = ones[0], q = rhs ? ones[1] : -ones[1];
                original.push_back(p);
                original.push_back(q);
                xor_clause_flag = true;
            }
            else assert(ones.size() <= 2);

            if (ones.size() >= 1) 
            {
                add_original_lit(0);
                original.clear();
                //clauses[clauses.size() - 1]->pri_clause();
            }
            xor_clause_flag = false;
            NextRow: ;
        }
        mzd_free(mat);
    }
    cout << "c Gauss elimination done : " << clause_id << endl;
    
    return true;
}


int Internal::gauss_old_elimination()
{
    cout << "c Gauss elimination start : " << clause_id << endl;
    int rows = xor_clauses.size();
    int cols = max_var + 1;
    mzd_t* mat = mzd_init(rows, cols);
    for (int row = 0 ; row < rows; row++)
    {
        Clause *c = xor_clauses[row];
        for (int i = 0 ; i < c->size; i ++)
        {
            int lit = c->literals[i];
            mzd_write_bit(mat, row, abs(lit) - 1, 1);
        }
        mzd_write_bit(mat, row, cols - 1, 1);
    }
    // printf("Matrix %dx%d:\n", mat->nrows, mat->ncols);
    // for (int row = 0; row < mat->nrows; row++) {
    //     for (int col = 0; col < mat->ncols; col++) {
    //         printf("%d ", mzd_read_bit(mat, row, col));
    //     }
    //     printf("\n");
    // }
    mzd_echelonize(mat, true);
    for (int row = 0 , rhs ; row < rows; row ++)
    {
        vector<int> ones;
        int64_t id;
        for (int col = 0; col < cols - 1; col ++)
        {
            if (mzd_read_bit(mat, row, col))
            {
                assert(mat != nullptr);
                assert(row >= 0 && row < mat->nrows);
                assert(col >= 0 && col < mat->ncols);
                if (ones.size() == 2) goto NextRow;
                ones.push_back(col + 1);
            }
        }

        rhs = mzd_read_bit(mat, row, cols - 1);

        original.clear();
        if (ones.size() == 1)
        {
            original.push_back(ones[0] * (rhs ? 1 : -1));
        }
        else if (ones.size() == 2)
        {
            int p = ones[0], q = rhs ? ones[1] : -ones[1];
            original.push_back(p);
            original.push_back(q);
            xor_clause_flag = true;
        }
        else assert(ones.size() <= 2);

        if (ones.size() >= 1) 
        {
            add_original_lit(0);
            original.clear();
            //clauses[clauses.size() - 1]->pri_clause();
        }
        xor_clause_flag = false;
        NextRow: ;
    }
    mzd_free(mat);
    cout << "c Gauss elimination done : " << clause_id << endl;
    
    return true;
}

}
