/*
 ApproxMC

 Copyright (c) 2009-2018, Mate Soos. All rights reserved.
 Copyright (c) 2015, Supratik Chakraborty, Daniel J. Fremont,
 Kuldeep S. Meel, Sanjit A. Seshia, Moshe Y. Vardi
 Copyright (c) 2014, Supratik Chakraborty, Kuldeep S. Meel, Moshe Y. Vardi

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 */


#ifndef AppMC_H_
#define AppMC_H_

#include "approxmcconfig.h"
#include <fstream>
#include <random>
#include <map>
#include <cstdint>
#include <cryptominisat5/cryptominisat.h>

using std::string;
using std::vector;
using namespace CMSat;

struct SATCount {
    void clear()
    {
        SATCount tmp;
        *this = tmp;
    }
    uint32_t hashCount = 0;
    uint32_t cellSolCount = 0;
};

class AppMC {
public:
    AppMC()
    {
    }

    ~AppMC()
    {
    }

    int solve(AppMCConfig _conf);
    string GenerateRandomBits(const uint32_t size, const uint32_t numhashes);
    string binary(const uint32_t x, const uint32_t length);
    bool gen_rhs();
    uint32_t loThresh;
    uint32_t hiThresh;
    SATSolver* solver = NULL;
    SATSolver* exSolver = NULL;
    void build_hitmaps(const string& filename);
    void printVersionInfo() const;

private:
    AppMCConfig conf;
    bool count(SATCount& count);
    void add_scalmc_options();
    bool ScalAppMC(SATCount& count);
    bool add_hash(uint32_t num_xor_cls, vector<Lit>& assumps, vector<Lit>& exAssumps, uint32_t total_num_hashes);
    void SetHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, std::map<uint64_t,Lit>& exHashVars, vector<Lit>& assumps, vector<Lit>& exAssumps);
    int correctReturnValue(const lbool ret) const;

    int64_t bounded_sol_count(
        uint32_t maxSolutions,
        const vector<Lit>& assumps,
        const uint32_t hashCount,
        vector<vector<Lit>> exploredInCell
    );

    void readInAFile(SATSolver* solver2, const string& filename);
    void readInStandardInput(SATSolver* solver2);


    double startTime;
    std::map< std::string, std::vector<uint32_t>> globalSolutionMap;
    void openLogFile();
    void call_after_parse();

    std::ofstream logfile;
    std::mt19937 randomEngine;
    double total_runtime; //runTime

    int argc;
    char** argv;

    //exSolver datastructures
    vector<vector<Lit>> bounded_ex_sol_count(
        uint32_t maxSolutions,
        const vector<Lit>& assumps,
        const uint32_t hashCount
    );
    void ex_block_down(vector<uint32_t>& ss);
    vector<lbool> ex_model_extension(vector<lbool> model);
    vector<uint32_t> ex_controls;
    vector<vector<uint32_t>> hitmap_pos;
    vector<vector<uint32_t>> hitmap_neg;
    vector<vector<bool>> ss_history;
    vector<vector<int>> ss_clauses;
};


#endif //AppMC_H_
