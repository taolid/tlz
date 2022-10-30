#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <boost/dynamic_bitset.hpp>

using namespace std;

#define RUN_LENGTH 8
#define RUN_LENGTH_MAX 255

size_t lastnode = 0;

void init_wt(vector<boost::dynamic_bitset<>> &wt, vector<size_t> T, size_t index)
{

    vector<size_t> char_count(256, 0);

    size_t low, high, mid;

    for (size_t i = 0; i < T.size(); i++)
    {
        char_count[T[i]]++;
    }

    for (size_t i = 0; i < char_count.size(); i++)
    {
        if (char_count[i] == 0)
        {
            wt[0].push_back(0);
        }
        else if (char_count[i] > 0)
        {
            wt[0].push_back(1);
        }
    }

    for (size_t i = 1; i < char_count.size(); i++)
    {
        if (char_count[i] != 0)
        {
            low = i;
            break;
        }
    }

    for (size_t i = char_count.size() - 1; i >= 0; i--)
    {
        if (char_count[i] != 0)
        {
            high = i;
            break;
        }
    }

    if (low == high)
    {
        return;
    }

    mid = (low + high) / 2;

    for (size_t i = 0; i < T.size(); i++)
    {
        if (T[i] <= mid)
        {
            wt[index].push_back(0);
        }
        else
        {
            wt[index].push_back(1);
        }
    }

    size_t num_1 = wt[index].count();
    size_t num_0 = wt[index].size() - num_1;

    vector<size_t> left_T;
    vector<size_t> right_T;

    for (size_t i = 0; i < wt[index].size(); i++)
    {
        if (wt[index][i] == 0)
        {
            left_T.push_back(T[i]);
        }
        else
        {
            right_T.push_back(T[i]);
        }
    }

    if (index > lastnode)
    {
        lastnode = index;
    }

    init_wt(wt, left_T, index * 2);
    init_wt(wt, right_T, index * 2 + 1);
}

void compress_bitset(boost::dynamic_bitset<> &B)
{
    size_t counter = 0;
    boost::dynamic_bitset<> temp;
    temp.push_back(B[0]);

    auto last = B[0];

    for (size_t j = 0; j < B.size(); j++)
    {
        auto bit = B[j];
        if (bit != last)
        {
            for (size_t i = 0; i < RUN_LENGTH; i++)
            {
                bool temp_bit = (counter >> (RUN_LENGTH - i - 1)) & 1;
                temp.push_back(temp_bit);
            }

            counter = 1;
        }
        else if (bit == last)
        {
            counter++;
            if (counter < RUN_LENGTH_MAX)
            {
                ;
            }
            else if (counter == RUN_LENGTH_MAX)
            {
                for (size_t i = 0; i < RUN_LENGTH; i++)
                {
                    bool temp_bit = (counter >> (RUN_LENGTH - i - 1)) & 1;
                    temp.push_back(temp_bit);
                }
                for (size_t i = 0; i < RUN_LENGTH; i++)
                {
                    temp.push_back(0);
                }

                counter = 0;
            }
        }
        if (j == B.size() - 1)
        {
            for (size_t i = 0; i < RUN_LENGTH; i++)
            {
                bool temp_bit = (counter >> (RUN_LENGTH - i - 1)) & 1;
                temp.push_back(temp_bit);
            }
        }
        last = bit;
    }

    B.resize(0);
    for (size_t i = 0; i < temp.size(); i++)
    {
        B.push_back(temp[i]);
    }
}

void compress_bitset_gamma(boost::dynamic_bitset<> &B)
{
    size_t counter = 0;
    boost::dynamic_bitset<> temp;
    temp.push_back(B[0]);

    auto last = B[0];

    for (size_t j = 0; j < B.size(); j++)
    {
        auto bit = B[j];
        if (bit != last)
        {
            size_t l = log2(counter);
            for (size_t i = 0; i < l; i++)
            {
                temp.push_back(0);
            }

            for (size_t i = 0; i < l + 1; i++)
            {
                bool temp_bit = (counter >> (l - i)) & 1;
                temp.push_back(temp_bit);
            }

            counter = 1;
        }
        else if (bit == last)
        {
            counter++;
        }

        if (j == B.size() - 1)
        {
            size_t l = log2(counter);
            for (size_t i = 0; i < l; i++)
            {
                temp.push_back(0);
            }

            for (size_t i = 0; i < l + 1; i++)
            {
                bool temp_bit = (counter >> (l - i)) & 1;
                temp.push_back(temp_bit);
            }
        }

        last = bit;
    }

    B.resize(0);
    for (size_t i = 0; i < temp.size(); i++)
    {
        B.push_back(temp[i]);
    }
}

void compress(vector<boost::dynamic_bitset<>> &wt)
{
    for (size_t i = 0; i <= lastnode; i++)
    {
        if (wt[i].size() != 0)
        {
            compress_bitset(wt[i]);
        }
    }
}

void compress_gamma(vector<boost::dynamic_bitset<>> &wt)
{
    for (size_t i = 0; i <= lastnode; i++)
    {
        if (wt[i].size() != 0)
        {
            compress_bitset_gamma(wt[i]);
        }
    }
}

void write_bitset(boost::dynamic_bitset<> B, ofstream &out)
{
    uint8_t bits = 0;
    for (size_t i = 0, j = 0; i < B.size(); i++)
    {
        bool temp = B[i];
        bits = bits << 1;
        bits = bits | temp;
        j++;
        if (j == 8)
        {
            out << bits;
            bits = 0;
            j = 0;
        }
    }
}

void write_wt(vector<boost::dynamic_bitset<>> &wt, const char *output_name)
{

    ofstream out(output_name, ofstream::app | ofstream::out | ofstream::binary);

    write_bitset(wt[0], out);

    for (size_t i = 0; i <= lastnode; i++)
    {
        if (wt[i].size() != 0)
        {
            size_t bit_num = wt[i].size();
            out << bit_num;
            write_bitset(wt[i], out);
        }
    }
}
