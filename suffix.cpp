/*
MIT License

Copyright (c) 2021 Tianyi Shi

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/
#include <algorithm>
#include <cstddef>
#include <iostream>
#include <span>
#include <tuple>
#include <cmath>
#include <random>
#include <vector>
#include <limits>
#include <fstream>

using namespace std;

using Character = uint32_t;

constexpr std::size_t EMPTY = numeric_limits<std::size_t>::max();
constexpr std::size_t UNIQUE = numeric_limits<std::size_t>::max() - 1;
constexpr std::size_t MULTI = numeric_limits<std::size_t>::max() - 2;

template <class T>
class Solver
{
public:
    span<T, dynamic_extent> t;
    span<std::size_t, dynamic_extent> sa;
    T sigma;
    std::size_t n;
    Solver(span<T, dynamic_extent> t, span<std::size_t, dynamic_extent> sa, T sigma) : t(t), sa(sa), sigma(sigma)
    {
        n = t.size();
    }

    void solve(bool recursive)
    {
        // cout << "Renaming..." << endl;
        rename();
        auto n1 = sort_lms_chars();
        // cout << "n1: " << n1 << endl;
        if (n1 == 1)
        {
            induced_sort_all();
        }
        else
        {
            induced_sort_all(); // sort LMS substrs
            if (!recursive)
            {
                // cout << "Retaining LMSs..." << endl;
                retain_sorted_lms_substrs();
                // cout << "Induced sorting all suffixes (bottom of recursion)" << endl;
                induced_sort_all();
                return;
            }
            else
            {
                std::size_t e = move_sorted_lms_substrs_to_the_end();
                auto [max_rank, has_ties] = construct_t1(e);
                // cout << "T1 max rank: " << max_rank << "; has ties: " << has_ties << endl;
                auto t1 = sa.subspan(0, n1);
                auto sa1 = sa.subspan(n - n1, n1);
                fill(sa1.begin(), sa1.end(), 0); // prepare for renaming
                Solver<std::size_t> subproblem = Solver<std::size_t>(t1, sa1, max_rank);
                subproblem.solve(has_ties);
                // cout << "Moving T1 result from SA1 to the head" << endl;
                for (std::size_t i = 0; i < n1; i++)
                {
                    sa[i] = sa1[i];
                }
                // cout << "Putting all LMS chars (unsorted) to the end..." << endl;
                auto lms = sa1;         // for readability
                std::size_t j = n1 - 1; // tail pointer
                lms[j] = n - 1;         // sentinel
                j -= 1;
                bool ti_is_s = false; // T[n-2] must be L
                bool tim1_is_s;
                T ti = t[n - 2];
                T tim1;
                std::size_t i = n - 2;
                for (std::size_t im1 = n - 2; im1-- > 0;)
                {
                    tim1 = t[im1];
                    tim1_is_s = tim1 < ti || (tim1 == ti && ti_is_s);
                    if (!tim1_is_s && ti_is_s)
                    {
                        lms[j] = i;
                        if (j == 0)
                        {
                            break;
                        }
                        j -= 1;
                    }
                    i = im1;
                    ti = tim1;
                    ti_is_s = tim1_is_s;
                }
                // cout << "Sorting LMS substrs in SA[0..n1), using `sa[i = lms[sa[i]]`..." << endl;
                std::size_t *sa_i;
                for (std::size_t i = 0; i < n1; i++)
                {
                    sa_i = &sa[i];
                    *sa_i = lms[*sa_i];
                }
                fill(lms.begin(), lms.end(), EMPTY);
                // cout << "Placing sorted LMS substrs back to corresponding buckets..." << endl;
                std::size_t sa_i_val;
                std::size_t curr_tail = 0; // dummy
                std::size_t offset = 0;
                for (std::size_t i = n1; i-- > 1;)
                {
                    sa_i = &sa[i];
                    sa_i_val = *sa_i;
                    *sa_i = EMPTY;
                    j = t[sa_i_val];
                    if (j == curr_tail)
                    {
                        offset += 1;
                    }
                    else
                    {
                        curr_tail = j;
                        offset = 0;
                    }
                    sa[curr_tail - offset] = sa_i_val;
                }
                // cout << "Induced sorting all suffixes..." << endl;
                induced_sort_all();
            }
        }
    }

    void rename()
    {
        // idx 0 to sigma inclusive should be filled with 0
        for (auto &c : t)
        {
            sa[c] += 1;
        }

        // compute head indices
        std::size_t prev = 1; // or sa[0]; the sentinel always occurs once
        std::size_t *curr;
        for (std::size_t i = 1; i < sigma; i++)
        {
            curr = &sa[i];
            *curr += prev;
            prev = *curr;
        }
        // rename
        for (auto c = t.begin(); c < t.end() - 1; c++)
        {
            *c = sa[*c - 1];
        }
        // clear sa
        fill(sa.begin(), sa.begin() + sigma + 1, 0);
        // count occurence
        for (auto &&c : t)
        {
            sa[c] += 1;
        }
        // compute all tail indices (inclusive)
        prev = 0; // tail of bucket 0 is always 0 (sentinel)
        for (std::size_t i = 1; i < n; i++)
        {
            curr = &sa[i];
            *curr += prev;
            prev = *curr;
        }

        bool tip1_is_s = true; // the last char (sentinel) is always S
        T tip1 = 0;
        T *t_i;
        for (std::size_t i = n - 1; i-- > 0;)
        {
            t_i = &t[i];
            tip1_is_s = (*t_i < tip1 || (*t_i == tip1 && tip1_is_s));
            // now tip1_is_s means ti_is_s
            if (tip1_is_s)
            {
                *t_i = sa[*t_i];
            }
            tip1 = *t_i;
        }
        // fill SA with EMPTY for subsequent steps
        fill(sa.begin(), sa.end(), EMPTY);
    }

    bool place_i_into_sa_ti_right_to_left(std::size_t i, T ti)
    {
        bool shifted = false;
        std::size_t *sa_ti = &sa[ti];
        switch (*sa_ti)
        {
        case UNIQUE:
            *sa_ti = i;
            break;
        case MULTI:
        {
            std::size_t *counter = &sa[ti - 1];
            if (*counter == EMPTY)
            {
                if (ti >= 2)
                {
                    std::size_t *sa_tim2 = &sa[ti - 2];
                    if (*sa_tim2 == EMPTY)
                    {
                        *sa_tim2 = i;
                        *counter = 1;
                        return false;
                    }
                }
                *sa_ti = i;
                *counter = EMPTY;
            }
            else
            {
                if (ti >= *counter + 2)
                {
                    std::size_t *x = &sa[ti - *counter - 2];
                    if (*x == EMPTY)
                    {
                        *x = i;
                        *counter += 1;
                        return false;
                    }
                }
                std::size_t counter_v = *counter;
                std::size_t left_bound = ti - counter_v + 1;
                for (std::size_t j = ti; j >= left_bound; j--)
                {
                    sa[j] = sa[j - 2];
                }
                sa[ti - counter_v] = i;
                sa[ti - counter_v - 1] = EMPTY;
                shifted = true;
            }
            break;
        }
        default:
        {
            std::size_t j = ti;
            while (sa[j] != EMPTY)
            {
                j--;
            }
            sa[j] = i;
            break;
        }
        }
        return shifted;
    }

    bool place_i_into_sa_ti_left_to_right(std::size_t i, T ti)
    {
        // cout << "Placing " << i << " into " << ti << endl;
        bool shifted = false;
        std::size_t *sa_ti = &sa[ti];
        switch (*sa_ti)
        {
        case UNIQUE:
            *sa_ti = i;
            break;
        case MULTI:
        {
            std::size_t *counter = &sa[ti + 1];
            if (*counter == EMPTY)
            {
                std::size_t j = ti + 2;
                if (j < sa.size())
                {
                    std::size_t *sa_tip2 = &sa[j];
                    if (*sa_tip2 == EMPTY)
                    {
                        *sa_tip2 = i;
                        *counter = 1;
                        return false;
                    }
                }
                *sa_ti = i;
                *counter = EMPTY;
            }
            else
            {
                std::size_t j = ti + *counter + 2;
                if (j < sa.size())
                {
                    std::size_t *x = &sa[j];
                    if (*x == EMPTY)
                    {
                        *x = i;
                        *counter += 1;
                        return false;
                    }
                }
                std::size_t counter_v = *counter;
                std::size_t right_bound = ti + counter_v;
                for (std::size_t j = ti; j < right_bound; j++)
                {
                    sa[j] = sa[j + 2];
                }
                sa[ti + counter_v] = i;
                sa[ti + counter_v + 1] = EMPTY;
                shifted = true;
            }
            break;
        }
        default:
        {
            std::size_t j = ti;
            while (sa[j] != EMPTY)
            {
                j++;
            }
            sa[j] = i;
            break;
        }
        }
        return shifted;
    }

    std::size_t sort_lms_chars()
    {
        bool ti_is_s = false; // T[n-2] must be L
        bool tim1_is_s;
        T ti = t[n - 2];
        T tim1;
        std::size_t *sa_ti;
        for (std::size_t im1 = n - 2; im1-- > 0;)
        {
            tim1 = t[im1];
            tim1_is_s = tim1 < ti || (tim1 == ti && ti_is_s);
            if (!tim1_is_s && ti_is_s)
            {
                // T[i] is LMS
                sa_ti = &sa[ti];
                switch (*sa_ti)
                {
                case EMPTY:
                    *sa_ti = UNIQUE;
                    break;
                case UNIQUE:
                    *sa_ti = MULTI;
                    break;
                default:
                    break;
                }
            }
            ti = tim1;
            ti_is_s = tim1_is_s;
        }
        sa[0] = n - 1;             // sentinel
        std::size_t lms_count = 1; // including sentinel
        ti_is_s = false;
        ti = t[n - 2];
        std::size_t i = n - 2;
        for (std::size_t im1 = n - 2; im1-- > 0;)
        {
            tim1 = t[im1];
            tim1_is_s = tim1 < ti || (tim1 == ti && ti_is_s);
            if (!tim1_is_s && ti_is_s)
            {
                place_i_into_sa_ti_right_to_left(i, ti);
                lms_count++;
            }
            ti = tim1;
            ti_is_s = tim1_is_s;
            i = im1;
        }

        // Remove MULTI and counters
        i = n - 1;
        std::size_t count;
        std::size_t left_bound;
        while (i != 0)
        {
            if (sa[i] == MULTI)
            {
                count = sa[i - 1];
                left_bound = i - count + 1;
                for (std::size_t j = i; j >= left_bound; j--)
                {
                    sa[j] = sa[j - 2];
                }
                i -= count;
                sa[i] = EMPTY;
                i -= 1;
                sa[i] = EMPTY;
            }
            i--;
        }
        return lms_count;
    }

    void induced_sort_all()
    {
        // cout << "Induced sorting..." << endl;
        // cout << "  Initialising SA for sorting L-type..." << endl;
        bool tip1_is_s = true; // the last char (sentinel) is always S
        T tip1 = 0;
        T *t_i;
        std::size_t *sa_ti;
        for (std::size_t i = n - 1; i-- > 0;)
        {
            t_i = &t[i];
            tip1_is_s = (*t_i < tip1 || (*t_i == tip1 && tip1_is_s));
            if (!tip1_is_s)
            {
                // ti is L
                sa_ti = &sa[*t_i];
                if (*sa_ti == EMPTY)
                {
                    *sa_ti = UNIQUE;
                }
                else if (*sa_ti == UNIQUE)
                {
                    *sa_ti = MULTI;
                }
            }
            tip1 = *t_i;
        }
        // cout << "  Induced-sorting L-type" << endl;
        std::size_t i = 0;
        std::size_t shifted_bucket_head = EMPTY; // dummy value
        std::size_t sa_i;
        while (i < n)
        {
            sa_i = sa[i];
            if (sa_i == MULTI)
            {
                shifted_bucket_head = i;
                i += 2;
                continue;
            }
            if (sa_i < UNIQUE && sa_i > 0)
            {
                std::size_t j = sa_i - 1;
                T tj = t[j];
                bool suf_j_is_l = tj >= t[sa_i];
                if (suf_j_is_l)
                {
                    if (place_i_into_sa_ti_left_to_right(j, tj))
                    {
                        if (shifted_bucket_head == tj)
                        {
                            i -= 1;
                            continue;
                        }
                    }
                }
            }
            i += 1;
        }
        // cout << "  Removing MULTI and counters..." << endl;
        std::size_t c;
        i = 1; // do not touch sentinel at idx 0
        while (i < n)
        {
            if (sa[i] == MULTI)
            {
                c = sa[i + 1];
                for (std::size_t j = i; j < i + c; j++)
                {
                    sa[j] = sa[j + 2];
                }
                i += c;
                sa[i] = EMPTY;
                i++;
                sa[i] = EMPTY;
            }
            i++;
        }
        // cout << "  Removing LMS indexes..." << endl;
        remove_lms();
        // cout << "  Initialising SA for sorting S-type..." << endl;
        tip1_is_s = true; // the last char (sentinel) is always S
        tip1 = 0;
        for (std::size_t i = n - 1; i-- > 0;)
        {
            t_i = &t[i];
            tip1_is_s = (*t_i < tip1 || (*t_i == tip1 && tip1_is_s));
            if (tip1_is_s)
            {
                // ti is S
                sa_ti = &sa[*t_i];
                if (*sa_ti == EMPTY)
                {
                    *sa_ti = UNIQUE;
                }
                else if (*sa_ti == UNIQUE)
                {
                    *sa_ti = MULTI;
                }
            }
            tip1 = *t_i;
        }
        // cout << "  Induced-sorting S-type" << endl;
        i = n - 1;
        shifted_bucket_head = EMPTY; // dummy value
        while (i != 0)
        {
            sa_i = sa[i];
            if (sa_i == MULTI)
            {
                shifted_bucket_head = i;
                i -= 2;
                continue;
            }
            if (sa_i < UNIQUE && sa_i > 0)
            {
                std::size_t j = sa_i - 1;
                T tj = t[j];
                bool suf_j_is_s = false;
                if (tj < t[sa_i])
                {
                    suf_j_is_s = true;
                }
                else if (tj == t[sa_i])
                {
                    if (tj > i)
                    {
                        suf_j_is_s = true;
                    }
                    else
                    {
                        std::size_t suspected_tail = tj;
                        std::size_t sa_tj = sa[suspected_tail];
                        suf_j_is_s = sa_tj == MULTI || suspected_tail < t[sa[suspected_tail + 1]];
                    }
                }
                if (suf_j_is_s)
                {
                    if (place_i_into_sa_ti_right_to_left(j, tj))
                    {
                        if (shifted_bucket_head == tj)
                        {
                            i += 1;
                            continue;
                        }
                    }
                }
            }
            i -= 1;
        }
    }

    void remove_lms()
    {
        bool ti_is_s = false; // T[n-2] must be L
        bool tim1_is_s;
        T ti = t[n - 2];
        T tim1;
        std::size_t *sa_ti;
        for (std::size_t im1 = n - 2; im1-- > 0;)
        {
            tim1 = t[im1];
            tim1_is_s = tim1 < ti || (tim1 == ti && ti_is_s);
            if (!tim1_is_s && ti_is_s)
            {
                // T[i] is LMS
                sa_ti = &sa[ti];
                switch (*sa_ti)
                {
                case MULTI:
                    sa[ti - 1] += 1;
                    break;
                case UNIQUE:
                    *sa_ti = MULTI;
                    sa[ti - 1] = 2; // set counter
                    break;
                default:
                    *sa_ti = UNIQUE;
                    break;
                }
            }
            ti = tim1;
            ti_is_s = tim1_is_s;
        }
        // don't touch sentinel
        std::size_t i = n - 1;
        std::size_t sa_i;
        while (i != 0)
        {
            sa_i = sa[i];
            switch (sa_i)
            {
            case UNIQUE:
            {
                sa[i] = EMPTY;
                i -= 1;
                break;
            }
            case MULTI:
            {
                std::size_t c = sa[i - 1];
                for (std::size_t j = i + 1 - c; j <= i; j++)
                {
                    sa[j] = EMPTY;
                }
                i -= c;
                break;
            }
            default:
            {
                i -= 1;
                break;
            }
            }
        }
    }

    void retain_sorted_lms_substrs()
    {
        // cout << "retaining sorted LMS substrs" << endl;
        std::size_t i = n - 1;
        std::size_t tail;
        std::size_t sa_i;
        auto is_s_type_bucket_tail = [this, &sa_i]()
        { return (*this).t[sa_i] < (*this).t[sa_i + 1]; };
        while (i > 0)
        {
            sa_i = sa[i];
            if (is_s_type_bucket_tail())
            {
                tail = i;
                while (true)
                {
                    if (sa_i != 0 && t[sa_i - 1] > t[sa_i])
                    {
                        // is LMS, retain
                    }
                    else
                    {
                        sa[i] = EMPTY;
                    }
                    i--;
                    if (i == 0)
                    {
                        return;
                    }
                    sa_i = sa[i];
                    if (t[sa_i] != tail)
                    {
                        if (is_s_type_bucket_tail())
                        {
                            tail = i;
                            continue;
                        }
                        else
                        {
                            break;
                        }
                    }
                }
            }
            // is L; empty
            sa[i] = EMPTY;
            i--;
        }
    }

    std::size_t move_sorted_lms_substrs_to_the_end()
    {
        // cout << "Moving sorted LMS substrs to the end of SA..." << endl;
        std::size_t i = n - 1;
        std::size_t end_pos = n - 1;
        std::size_t tail;
        std::size_t sa_i;
        auto is_s_type_bucket_tail = [this, &sa_i]()
        { return (*this).t[sa_i] < (*this).t[sa_i + 1]; };
        while (i > 0)
        {
            sa_i = sa[i];
            if (is_s_type_bucket_tail())
            {
                tail = i;
                while (true)
                {
                    if (sa_i != 0 && t[sa_i - 1] > t[sa_i])
                    {
                        // is LMS
                        sa[end_pos] = sa_i;
                        end_pos--;
                    }
                    i--;
                    if (i == 0)
                    {
                        goto endwhile;
                    }
                    sa_i = sa[i];
                    if (t[sa_i] != tail)
                    {
                        if (is_s_type_bucket_tail())
                        {
                            tail = i;
                            continue;
                        }
                        else
                        {
                            break;
                        }
                    }
                }
            }
            // is L; empty
            sa[i] = EMPTY;
            i--;
        }
    endwhile:
        sa[end_pos] = n - 1;
        fill(sa.begin(), sa.begin() + end_pos, EMPTY);
        return end_pos;
    }

    tuple<std::size_t, bool> construct_t1(std::size_t end_pos)
    {
        // cout << "Constructing T1..." << endl;
        auto length_of_lms_str = [this](std::size_t k)
        {
            T prev = this->t[k];
            T curr;
            std::size_t next_lms_index = 0; // dummy
            std::size_t i = k + 1;
            while (i != this->n)
            {
                curr = this->t[i];
                if (prev > curr)
                {
                    next_lms_index = i;
                }
                else if (prev < curr && next_lms_index != 0)
                {
                    return next_lms_index - k + 1;
                }
                prev = curr;
                i++;
            }
            // the case of the last LMS substring
            return this->n - k;
        };
        std::size_t prev_lms_len = 0; // sentinel actually has len of 1, but it is always smaller than the next LMS
        std::size_t curr_lms_len;
        std::size_t prev_lms_idx = 0; // dummy
        std::size_t curr_lms_idx;
        std::size_t rank = 0;
        bool has_ties = false;
        for (std::size_t i = end_pos + 1; i < n; i++)
        {
            curr_lms_idx = sa[i];
            curr_lms_len = length_of_lms_str(curr_lms_idx);
            if (curr_lms_len != prev_lms_len)
            {
                rank++;
            }
            else
            {
                bool identical = true;
                for (std::size_t i = 0; i < curr_lms_len; i++)
                {
                    if (t[prev_lms_idx + i] != t[curr_lms_idx + i])
                    {
                        identical = false;
                        break;
                    }
                }
                if (identical)
                {
                    has_ties = true;
                }
                else
                {
                    rank++;
                }
            }
            sa[curr_lms_idx / 2] = rank;
            prev_lms_len = curr_lms_len;
            prev_lms_idx = curr_lms_idx;
        }
        // collect t1
        std::size_t sa_i;
        std::size_t j = 0;
        for (std::size_t i = 0; i < end_pos; i++)
        {
            sa_i = sa[i];
            if (sa_i != EMPTY)
            {
                sa[j] = sa_i;
                j++;
            }
        }
        sa[j] = 0; // sentinel
        fill(sa.begin() + j + 1, sa.begin() + end_pos, EMPTY);
        return tuple{rank, has_ties};
    }

    void print_sa()
    {
        for (auto &&i : sa)
        {
            if (i == EMPTY)
            {
                cout << "E"
                     << " ";
            }
            else if (i == UNIQUE)
            {
                cout << "U"
                     << " ";
            }
            else if (i == MULTI)
            {
                cout << "M"
                     << " ";
            }
            else
            {
                cout << i << " ";
            }
        }
        cout << endl;
    }
    void print_t()
    {
        for (auto &&c : t)
        {
            cout << c << " ";
        }
        cout << endl;
    }
};

int cmpfunc(const void *a, const void *b)
{
    const char *ia = (const char *)a;
    const char *ib = (const char *)b;
    return strcmp(ia, ib);
}
