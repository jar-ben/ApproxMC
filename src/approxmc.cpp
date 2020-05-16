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

#include <ctime>
#include <cstring>
#include <errno.h>
#include <algorithm>
#include <string.h>
#include <sstream>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <set>
#include <fstream>
#include <sys/stat.h>
#include <string.h>
#include <list>
#include <array>
#include <cmath>
#include <complex>

#include "approxmc.h"
#include "time_mem.h"
#include "cryptominisat5/cryptominisat.h"
#include "cryptominisat5/solvertypesmini.h"
#include "GitSHA1.h"

using std::cout;
using std::cerr;
using std::endl;
using std::list;
using std::map;

void print_xor(const vector<uint32_t>& vars, const uint32_t rhs)
{
    cout << "[appmc] Added XOR ";
    for (size_t i = 0; i < vars.size(); i++) {
        cout << vars[i]+1;
        if (i < vars.size()-1) {
            cout << " + ";
        }
    }
    cout << " = " << (rhs ? "True" : "False") << endl;
}

void AppMC::openLogFile()
{
    if (!conf.logfilename.empty()) {
        logfile.open(conf.logfilename.c_str());
        if (!logfile.is_open()) {
            cout << "[appmc] Cannot open AppMC log file '" << conf.logfilename
                 << "' for writing." << endl;
            exit(1);
        }
    }
}

template<class T>
inline T findMedian(vector<T>& numList)
{
    std::sort(numList.begin(), numList.end());
    size_t medIndex = (numList.size() + 1) / 2;
    size_t at = 0;
    if (medIndex >= numList.size()) {
        at += numList.size() - 1;
        return numList[at];
    }
    at += medIndex;
    return numList[at];
}

template<class T>
inline T findMin(vector<T>& numList)
{
    T min = std::numeric_limits<T>::max();
    for (const auto a: numList) {
        if (a < min) {
            min = a;
        }
    }
    return min;
}

bool AppMC::add_hash(uint32_t num_xor_cls, vector<Lit>& assumps, vector<Lit>& exAssumps, uint32_t total_num_hashes)
{
    const string randomBits =
        GenerateRandomBits(conf.sampling_set.size() * num_xor_cls, total_num_hashes);

    bool rhs;
    vector<uint32_t> vars;
    vector<uint32_t> exVars;

    for (uint32_t i = 0; i < num_xor_cls; i++) {
        //new activation variable
        solver->new_var();
        exSolver->new_var();
        uint32_t act_var = solver->nVars()-1;
        assumps.push_back(Lit(act_var, true));
        uint32_t exAct_var = exSolver->nVars()-1;
        exAssumps.push_back(Lit(exAct_var, true));

        assert(std::find(ex_controls.begin(), ex_controls.end(), exAct_var) == ex_controls.end());

        vars.clear();
        exVars.clear();
        vars.push_back(act_var);
        exVars.push_back(exAct_var);
        rhs = gen_rhs();

        for (uint32_t j = 0; j < conf.sampling_set.size(); j++) {
            if (randomBits.at(conf.sampling_set.size() * i + j) == '1') {
                vars.push_back(conf.sampling_set[j]);
                exVars.push_back(conf.sampling_set[j]);
            }
        }
        exSolver->add_xor_clause(exVars, rhs);
        solver->add_xor_clause(vars, rhs);
        if (conf.verb_appmc_cls) {
            print_xor(vars, rhs);
        }
    }
    return true;
}

// We parse the input file again, which is definitively not the best approach here. This functionality should be provided by the solver (cryptominisat)
// The purpose of this function is to build hitmaps
// hitmap_pos[i] contains the list of clauses (ids of the clauses) that contain literal i + 1
// hitmap_neg[i] contains the list of clauses (ids of the clauses) that contain literal -(i + 1)
void AppMC::build_hitmaps(const string& path){
    std::ifstream infile(path, std::ifstream::in);

    vector<string> clauses_str;
    string line;
    string pom;
    int vars;
    while (getline(infile, line))
    {
            if (line[0] == 'p'){
                    std::istringstream is(line);
                    is >> pom;      // p
                    is >> pom;      // cnf
                    is >> vars;     //number of variables
            }
            else if(line[0] == 'c')
                    continue;
            else{
                    clauses_str.push_back(line);
            }
    }
    hitmap_pos.resize(vars);
    hitmap_neg.resize(vars);
    assert(clauses_str.size() <= conf.sampling_set.size());
    for(size_t i = 0; i < conf.sampling_set.size(); i++){
        std::istringstream is(clauses_str[i]);
        int lit;
        while(is >> lit && lit != 0){
            if(lit > 0)
                hitmap_pos[lit - 1].push_back(i);
            else
                hitmap_neg[(-1 * lit) - 1].push_back(i);	
	}
    }
}

void AppMC::ex_block_down(vector<uint32_t>& co_ss){
    exSolver->new_var();
    uint32_t act_var = exSolver->nVars()-1;
    for(auto var: co_ss){
        vector<Lit> cl;
        cl.push_back(Lit(act_var, true));
        cl.push_back(Lit(var, false));        
        exSolver->add_clause(cl);
        ss_clauses.push_back(vector<int>{act_var, var});
    }
    ex_controls.push_back(act_var);
}

vector<vector<Lit>> AppMC::bounded_ex_sol_count(
        uint32_t maxSolutions,
        const vector<Lit>& exAssumps,
        const uint32_t hashCount
) {
    cout << "[appmc] "
    "[ " << std::setw(7) << std::setprecision(2) << std::fixed
    << (cpuTimeTotal()-total_runtime)
    << " ]"
    << " bounded_ex_sol_count looking for " << std::setw(4) << maxSolutions << " solutions"
    << " -- hashes active: " << hashCount << endl;

    //Set up things for adding clauses that can later be removed
    vector<lbool> model;
    vector<Lit> new_assumps(exAssumps);
    exSolver->new_var();
    uint32_t act_var = exSolver->nVars()-1;
    new_assumps.push_back(Lit(act_var, true));

    //each var from ex_control corresponds to an activation (tseitin) variable corresponding to an already explored SS
    //here we sat that we are looking for a subset of one of the explored SSes
    vector<Lit> controls;
    for(auto var: ex_controls){
        controls.push_back(Lit(var, false));
    }
    controls.push_back(Lit(act_var, false));
    exSolver->add_clause(controls);

    if (hashCount > 2) {
        exSolver->simplify(&new_assumps);
    }

    vector<vector<Lit>> solutions;
    lbool ret;
    double last_found_time = cpuTimeTotal();
    while (solutions.size() < maxSolutions) {
        ret = exSolver->solve(&new_assumps);
        assert(ret == l_False || ret == l_True);
        if (ret != l_True) {
            break;
        }
        model = exSolver->get_model();

        if (solutions.size() < maxSolutions) {
            vector<Lit> lits;
            for (const uint32_t var: conf.sampling_set) {
                if (model[var] != l_Undef) {
                    lits.push_back(Lit(var, model[var] == l_True));
                } else {
                    assert(false);
                }
            }
            solutions.push_back(lits);
            lits.push_back(Lit(act_var, false));
            exSolver->add_clause(lits);
        }
    }

    //Remove clauses added
    vector<Lit> cl_that_removes;
    cl_that_removes.push_back(Lit(act_var, false));
    exSolver->add_clause(cl_that_removes);
    cout << "ex solutions: " << solutions.size() << endl;
    assert(ret != l_Undef);
    return solutions;
}

vector<lbool> AppMC::ex_model_extension(vector<lbool> model){
    vector<bool> extension(conf.sampling_set.size(), false);
    for(int var = 0; var < hitmap_pos.size(); var++){    
        if(var < conf.sampling_set.size()) continue; //we care only about the original literals    
        //assert that var is not in conf.sampling_set
        if(model[var] == l_True){
            for(auto c: hitmap_pos[var]){
                extension[c] = true;
            }
        }else{
            assert(model[var] == l_False);
            for(auto c: hitmap_neg[var]){
                extension[c] = true;
            }
        }
    }

    int ext_size = 0;
    for(int i = 0; i < extension.size(); i++){
        if(extension[i]){
            model[conf.sampling_set[i]] = l_False;
            ext_size++;
        }
    }
    ss_history.push_back(extension);    
    return model;
}

int64_t AppMC::bounded_sol_count(
        uint32_t maxSolutions,
        const vector<Lit>& assumps,
        const uint32_t hashCount,
        vector<vector<Lit>> exploredInCell
) {
    cout << "[appmc] "
    "[ " << std::setw(7) << std::setprecision(2) << std::fixed
    << (cpuTimeTotal()-total_runtime)
    << " ]"
    << " bounded_sol_count looking for " << std::setw(4) << maxSolutions << " solutions"
    << " -- hashes active: " << hashCount << endl;

    //Set up things for adding clauses that can later be removed
    vector<lbool> model;
    vector<Lit> new_assumps(assumps);
    solver->new_var();
    uint32_t act_var = solver->nVars()-1;
    new_assumps.push_back(Lit(act_var, true));

    for(auto lits: exploredInCell){
        lits.push_back(Lit(act_var, false));
        solver->add_clause(lits);
    }

    if (hashCount > 2) {
        solver->simplify(&new_assumps);
    }

    int64_t solutions = exploredInCell.size();
    lbool ret;
    double last_found_time = cpuTimeTotal();
    while (solutions < maxSolutions) {
        ret = solver->solve(&new_assumps);
        assert(ret == l_False || ret == l_True);

        if (conf.verb >=2 ) {
            cout << "[appmc] bounded_sol_count ret: " << std::setw(7) << ret;
            if (ret == l_True) {
                cout << " sol no.  " << std::setw(3) << solutions;
            } else {
                cout << " No more. " << std::setw(3) << "";
            }
            cout << " T: "
            << std::setw(7) << std::setprecision(2) << std::fixed << (cpuTimeTotal()-total_runtime)
            << " -- hashes act: " << hashCount
            << " -- T since last: "
            << std::setw(7) << std::setprecision(2) << std::fixed << (cpuTimeTotal()-last_found_time)
            << endl;
            last_found_time = cpuTimeTotal();
        }

        if (ret != l_True) {
            break;
        }
        model = solver->get_model();
        model = ex_model_extension(model);

        if (solutions < maxSolutions) {
            vector<Lit> lits;
            vector<uint32_t> ss;
            lits.push_back(Lit(act_var, false));
            for (const uint32_t var: conf.sampling_set) {
                if (model[var] != l_Undef) {
                    lits.push_back(Lit(var, model[var] == l_True));
                    if(model[var] == l_True) ss.push_back(var);
                } else {
                    assert(false);
                }
            }
            if (conf.verb_appmc_cls) {
                cout << "[appmc] Adding banning clause: " << lits << endl;
            }
            solver->add_clause(lits);
            ex_block_down(ss);
        }
        solutions++;
    }

    //Remove clauses added
    vector<Lit> cl_that_removes;
    cl_that_removes.push_back(Lit(act_var, false));
    solver->add_clause(cl_that_removes);

    assert(ret != l_Undef);
    return solutions;
}

bool AppMC::gen_rhs()
{
    std::uniform_int_distribution<uint32_t> dist{0, 1};
    bool rhs = dist(randomEngine);
    //cout << "rnd rhs:" << (int)rhs << endl;
    return rhs;
}

string AppMC::GenerateRandomBits(const uint32_t size, const uint32_t num_hashes)
{
    string randomBits;
    std::uniform_int_distribution<uint32_t> dist{0, 1000};
    uint32_t cutoff = 500;
    if (conf.sparse && num_hashes > 132) {
        double probability = 13.46*std::log(num_hashes)/num_hashes;
        assert(probability < 0.5);
        cutoff = std::ceil(1000.0*probability);
        cout << "[appmc] sparse hashing used, cutoff: " << cutoff << endl;
    }

    while (randomBits.size() < size) {
        bool val = dist(randomEngine) < cutoff;
        randomBits += '0' + val;
    }
    assert(randomBits.size() >= size);

    //cout << "rnd bits: " << randomBits << endl;
    return randomBits;
}

int AppMC::solve(AppMCConfig _conf)
{
    conf = _conf;
    build_hitmaps(conf.inputfile);
    openLogFile();
    randomEngine.seed(conf.seed);
    total_runtime = cpuTimeTotal();
    cout << "[appmc] Using start iteration " << conf.start_iter << endl;

    SATCount solCount;
    bool finished = count(solCount);
    assert(finished);

    cout << "[appmc] FINISHED AppMC T: " << (cpuTimeTotal() - startTime) << " s" << endl;
    if (solCount.hashCount == 0 && solCount.cellSolCount == 0) {
        cout << "[appmc] Formula was UNSAT " << endl;
    }

    if (conf.verb > 2) {
        solver->print_stats();
    }

    cout << "[appmc] Number of solutions is: "
    << solCount.cellSolCount
     << " x 2^" << solCount.hashCount << endl;

    return correctReturnValue(l_True);
}

void AppMC::SetHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, std::map<uint64_t,Lit>& exHashVars, vector<Lit>& assumps, vector<Lit>& exAssumps)
{
    assert(assumps.size() == exAssumps.size());
    if (clausNum < assumps.size()) {
        uint64_t numberToRemove = assumps.size()- clausNum;
        for (uint64_t i = 0; i<numberToRemove; i++) {
            assumps.pop_back();
            exAssumps.pop_back();
        }
    } else {
        if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
            for (uint32_t i = assumps.size(); i< hashVars.size() && i < clausNum; i++) {
                assumps.push_back(hashVars[i]);
                exAssumps.push_back(exHashVars[i]);
            }
        }
        if (clausNum > hashVars.size()) {
            add_hash(clausNum-hashVars.size(), assumps, exAssumps, clausNum);
            for (uint64_t i = hashVars.size(); i < clausNum; i++) {
                hashVars[i] = assumps[i];
                exHashVars[i] = exAssumps[i];
            }
        }
    }
}

bool AppMC::count(SATCount& count)
{
    count.clear();
    vector<uint64_t> numHashList;
    vector<int64_t> numCountList;
    vector<Lit> assumps;
    vector<Lit> exAssumps;

    uint64_t hashCount = conf.start_iter;
    uint64_t hashPrev = 0;
    uint64_t mPrev = 0;

    double myTime = cpuTimeTotal();
    cout << "[appmc] Starting up, initial measurement" << endl;
    if (hashCount == 0) {
        int64_t currentNumSolutions = bounded_sol_count(conf.threshold+1, assumps, count.hashCount, vector<vector<Lit>>());
        if (!conf.logfilename.empty()) {
            logfile << "appmc:"
            <<"0:0:"
            << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
            << (int)(currentNumSolutions == (conf.threshold + 1)) << ":"
            << currentNumSolutions << endl;
        }

        //Din't find at least threshold+1
        if (currentNumSolutions <= conf.threshold) {
            cout << "[appmc] Did not find at least threshold+1 (" << conf.threshold << ") we found only " << currentNumSolutions << ", exiting AppMC" << endl;
            count.cellSolCount = currentNumSolutions;
            count.hashCount = 0;
            return true;
        }
        hashCount++;
    }

    for (uint32_t j = 0; j < conf.measurements; j++) {
        cout << "     ==== " << j << " out of " << conf.measurements << endl;
        map<uint64_t,int64_t> countRecord;
        map<uint64_t,uint32_t> succRecord;
        map<uint64_t,Lit> hashVars; //map assumption var to XOR hash
        map<uint64_t,Lit> exHashVars; //map assumption var to XOR hash


        //Note, the rank of a random NxN matrix is not N of course. It has an expected
        //rank that is of course lower than N. So we need to shoot higher.
        //https://math.stackexchange.com/questions/324150/expected-rank-of-a-random-binary-matrix
        //Apparently this question is analyzed in Kolchin's book Random Graphs in sect. 3.2.
        //Thanks to Yash Pote to digging this one out. Very helpful.
        uint64_t total_max_xors = std::ceil((double)conf.sampling_set.size()*1.2)+5;

        uint64_t numExplored = 0;
        uint64_t lowerFib = 0;
        uint64_t upperFib = total_max_xors;

        while (numExplored < total_max_xors) {
            cout << "[appmc] Explored: " << std::setw(4) << numExplored
                 << " ind set size: " << std::setw(6) << conf.sampling_set.size() << endl;
            myTime = cpuTimeTotal();
            uint64_t swapVar = hashCount;
            SetHash(hashCount,hashVars,exHashVars,assumps,exAssumps);
            cout << "[appmc] hashes active: " << std::setw(6) << hashCount << endl;
            int64_t currentNumSolutions = 0;
            vector<vector<Lit>> exploredInCell;
            exploredInCell = bounded_ex_sol_count(conf.threshold + 1, exAssumps, hashCount);
            cout << "explored in cell: " << exploredInCell.size() << ", threshold: " << conf.threshold << endl;
            currentNumSolutions = exploredInCell.size();
            if(currentNumSolutions < conf.threshold + 1)
                currentNumSolutions = bounded_sol_count(conf.threshold + 1, assumps, hashCount, exploredInCell);

            //cout << currentNumSolutions << ", " << threshold << endl;
            if (!conf.logfilename.empty()) {
                logfile << "appmc:"
                << j << ":" << hashCount << ":"
                << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                << (int)(currentNumSolutions == (conf.threshold + 1)) << ":"
                << currentNumSolutions << endl;
            }
            cout << "   sols: " << currentNumSolutions << endl;
            if (currentNumSolutions <= conf.threshold) {
                numExplored = lowerFib + total_max_xors - hashCount;

                //check success record if it exists
                if (succRecord.find(hashCount-1) != succRecord.end()
                    && succRecord[hashCount-1] == 1
                ) {
                    numHashList.push_back(hashCount);
                    numCountList.push_back(currentNumSolutions);
                    mPrev = hashCount;
                    //less than threshold solutions
                    break;
                }

                //No success record
                succRecord[hashCount] = 0;
                countRecord[hashCount] = currentNumSolutions;
                if (std::abs<int64_t>((int64_t)hashCount - (int64_t)mPrev) <= 2
                    && mPrev != 0
                ) {
                    upperFib = hashCount;
                    hashCount--;
                } else {
                    if (hashPrev > hashCount) {
                        hashPrev = 0;
                    }
                    upperFib = hashCount;
                    if (hashPrev > lowerFib) {
                        lowerFib = hashPrev;
                    }
                    hashCount = (upperFib+lowerFib)/2;
                }
            } else {
                assert(currentNumSolutions == conf.threshold+1);
                numExplored = hashCount + total_max_xors - upperFib;

                //Check if success record for +1 hashcount exists and is 0
                if (succRecord.find(hashCount+1) != succRecord.end()
                    && succRecord[hashCount+1] == 0
                ) {
                    numHashList.push_back(hashCount+1);
                    numCountList.push_back(countRecord[hashCount+1]);
                    mPrev = hashCount+1;
                    break;
                }

                //No success record of hashCount+1 or it's not 0
                succRecord[hashCount] = 1;
                if (std::abs<int64_t>((int64_t)hashCount - (int64_t)mPrev) < 2
                    && mPrev!=0
                ) {
                    lowerFib = hashCount;
                    hashCount ++;
                } else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
                    lowerFib = hashCount;
                    hashCount = (lowerFib+upperFib)/2;
                } else {
                    //cout << "hashPrev: " << hashPrev << " hashCount: " << hashCount << endl;
                    hashCount = lowerFib + (hashCount -lowerFib)*2;
                }
            }
            hashPrev = swapVar;
        }
        assumps.clear();
        exAssumps.clear();
        hashCount = mPrev;
    }
    if (numHashList.size() == 0) {
        //UNSAT
        return true;
    }

    auto minHash = findMin(numHashList);
    auto cnt_it = numCountList.begin();
    for (auto hash_it = numHashList.begin()
        ; hash_it != numHashList.end() && cnt_it != numCountList.end()
        ; hash_it++, cnt_it++
    ) {
        *cnt_it *= pow(2, (*hash_it) - minHash);
    }
    int medSolCount = findMedian(numCountList);

    count.cellSolCount = medSolCount;
    count.hashCount = minHash;
    return true;
}

///////////
// Useful helper functions
///////////

void printVersionInfoAppMC()
{
    cout << "c AppMC SHA revision " << ::get_version_sha1() << endl;
    cout << "c AppMC version " << ::get_version_tag() << endl;
    cout << "c AppMC compilation env " << ::get_compilation_env() << endl;
    #ifdef __GNUC__
    cout << "c AppMC compiled with gcc version " << __VERSION__ << endl;
    #else
    cout << "c AppMC compiled with non-gcc compiler" << endl;
    #endif
}

void AppMC::printVersionInfo() const
{
    ::printVersionInfoAppMC();
    cout << solver->get_text_version_info();
}

int AppMC::correctReturnValue(const lbool ret) const
{
    int retval = -1;
    if (ret == l_True) {
        retval = 10;
    } else if (ret == l_False) {
        retval = 20;
    } else if (ret == l_Undef) {
        retval = 15;
    } else {
        std::cerr << "Something is very wrong, output is neither l_Undef, nor l_False, nor l_True" << endl;
        exit(-1);
    }

    return retval;
}
