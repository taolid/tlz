#include "suffix.cpp"
#include "mywt.cpp"

int main(int argc, char const *argv[])
{

    string filename, output_name;
    if (argc == 1)
    {
        printf("enter filename.");
        return -1;
    }

    filename = argv[1];
    output_name = filename + ".gama.lz";

    std::size_t T_len;
    char *T;
    ifstream infile;

    infile.open(filename.c_str(), ios::in);
    if (!infile)
    {
        printf("file not find.");
        exit(-1);
    }

    infile.seekg(0, ios::end);
    T_len = infile.tellg();

    T = new char[T_len + 1]();
    infile.seekg(0, ios::beg);
    infile.read(T, T_len);
    T[T_len] = 0;

    infile.close();

    uint32_t sigma = 256;
    std::size_t n = T_len;

    vector<uint32_t> t(n + 1);
    for (std::size_t i = 0; i < n; i++)
    {
        t[i] = (uint32_t)T[i];
    }
    t[n] = 0;

    vector<std::size_t> sa(n + 1, 0);

    auto solver = Solver(span(t), span(sa), sigma);
    solver.solve(true);

    vector<std::size_t> bwt(n + 1, 0);
    std::size_t bwt_len = bwt.size();
    for (std::size_t i = 0; i < bwt_len; i++)
    {
        bwt[i] = T[(sa[i] - 1 + (n + 1)) % (n + 1)];
    }

    vector<boost::dynamic_bitset<>> wt;
    wt.reserve(T_len);
    init_wt(wt, bwt, 1);

    compress_gamma(wt);

    write_wt(wt, output_name.c_str());
}