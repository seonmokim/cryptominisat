/*
 * CUSP and ScalMC
 *
 * Copyright (c) 2009-2015, Mate Soos. All rights reserved.
 * Copyright (c) 2014, Supratik Chakraborty, Kuldeep S. Meel, Moshe Y. Vardi
 * Copyright (c) 2015, Supratik Chakraborty, Daniel J. Fremont,
 * Kuldeep S. Meel, Sanjit A. Seshia, Moshe Y. Vardi
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation
 * version 2.0 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
 */

#if defined(__GNUC__) && defined(__linux__)

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <fenv.h>
#endif

#include <stdio.h>
#include <ctime>
#include <cstring>
#include <errno.h>
#include <string.h>
#include <sstream>
#include <iostream>
#include <iomanip>
#include <map>
#include <set>
#include <fstream>
#include <sys/stat.h>
#include <string.h>
#include <list>
#include <array>

#include "scalmc.h"
#include "time_mem.h"
#include "dimacsparser.h"
#include "cryptominisat5/cryptominisat.h"
#include "signalcode.h"

#include <assert.h>
#include <math.h>
#include <stdlib.h>

extern "C" { 
    #include "asa241.h" 
}

using std::cout;
using std::cerr;
using std::endl;
using boost::lexical_cast;
using std::list;
using std::map;

string binary(unsigned x, uint32_t length)
{
    uint32_t logSize = (x == 0 ? 1 : log2(x) + 1);
    string s;
    do {
        s.push_back('0' + (x & 1));
    } while (x >>= 1);
    for (uint32_t i = logSize; i < (uint32_t) length; i++) {
        s.push_back('0');
    }
    std::reverse(s.begin(), s.end());

    return s;

}

string CUSP::GenerateRandomBits(uint32_t size)
{
    string randomBits;
    std::uniform_int_distribution<unsigned> uid {0, 2147483647U};
    uint32_t i = 0;
    while (i < size) {
        i += 31;
        randomBits += binary(uid(randomEngine), 31);
    }
    return randomBits;
}

void CUSP::add_approxmc_options()
{
    approxMCOptions.add_options()
    ("mode", po::value(&searchMode)->default_value(searchMode)
        ,"Search mode. ApproxMC = 0, ScalMC = 1, SearchMC = 2")
    ("pivotAC", po::value(&pivotApproxMC)->default_value(pivotApproxMC)
        , "Number of solutions to check for")
        ("tApproxMC", po::value(&tApproxMC)->default_value(tApproxMC)
        , "Number of measurements")
    ("startIteration", po::value(&startIteration)->default_value(startIteration), "")
    ("looptout", po::value(&loopTimeout)->default_value(loopTimeout)
        , "Timeout for one measurement, consisting of finding pivotAC solutions")
    ("cuspLogFile", po::value(&cuspLogFile)->default_value(cuspLogFile),"")
    ("unset", po::value(&unset_vars)->default_value(unset_vars),
     "Try to ask the solver to unset some independent variables, thereby"
     "finding more than one solution at a time")
    ;

    help_options_simple.add(approxMCOptions);
    help_options_complicated.add(approxMCOptions);
}

void CUSP::add_searchmc_options()
{
    searchMCOptions.add_options()
    ("cl", po::value(&cl)->default_value(cl)
        , "Confidence level")
    ("thres", po::value(&thres)->default_value(thres)
        , "Threshold value (Maximum interval width)")
    ;

    help_options_simple.add(searchMCOptions);
    help_options_complicated.add(searchMCOptions);
}

void CUSP::add_supported_options()
{
    Main::add_supported_options();
    add_approxmc_options();
    add_searchmc_options();
}

void print_xor(const vector<uint32_t>& vars, const uint32_t rhs)
{
    cout << "Added XOR ";
    for (size_t i = 0; i < vars.size(); i++) {
        cout << vars[i]+1;
        if (i < vars.size()-1) {
            cout << " + ";
        }
    }
    cout << " = " << (rhs ? "True" : "False") << endl;
}

bool CUSP::openLogFile()
{
    cusp_logf.open(cuspLogFile.c_str());
    if (!cusp_logf.is_open()) {
        cout << "Cannot open CUSP log file '" << cuspLogFile
             << "' for writing." << endl;
        exit(1);
    }
    return true;
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

bool CUSP::AddHash(uint32_t num_xor_cls, vector<Lit>& assumps)
{
    string randomBits = GenerateRandomBits((independent_vars.size() + 1) * num_xor_cls);
    bool rhs = true;
    vector<uint32_t> vars;

    for (uint32_t i = 0; i < num_xor_cls; i++) {
        //new activation variable
        solver->new_var();
        uint32_t act_var = solver->nVars()-1;
        assumps.push_back(Lit(act_var, true));

        vars.clear();
        vars.push_back(act_var);
        rhs = (randomBits[(independent_vars.size() + 1) * i] == 1);

        for (uint32_t j = 0; j < independent_vars.size(); j++) {
            if (randomBits[(independent_vars.size() + 1) * i + j] == '1') {
                vars.push_back(independent_vars[j]);
            }
        }
        solver->add_xor_clause(vars, rhs);
        if (conf.verbosity >= 3) {
            print_xor(vars, rhs);
        }
    }
    return true;
}

int64_t CUSP::BoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps)
{
    cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;

    //Set up things for adding clauses that can later be removed
    solver->new_var();
    uint32_t act_var = solver->nVars()-1;
    vector<Lit> new_assumps(assumps);
    new_assumps.push_back(Lit(act_var, true));

    double start_time = cpuTime();
    uint64_t solutions = 0;
    lbool ret;
    while (solutions < maxSolutions) {
        //solver->set_max_confl(10*1000*1000);
        double this_iter_timeout = loopTimeout-(cpuTime()-start_time);
        solver->set_timeout_all_calls(this_iter_timeout);
        ret = solver->solve(&new_assumps);
        if (ret != l_True)
            break;

        size_t num_undef = 0;
        if (solutions < maxSolutions) {
            vector<Lit> lits;
            lits.push_back(Lit(act_var, false));
            for (const uint32_t var: independent_vars) {
                if (solver->get_model()[var] != l_Undef) {
                    lits.push_back(Lit(var, solver->get_model()[var] == l_True));
                } else {
                    num_undef++;
                }
            }
            solver->add_clause(lits);
        }
        if (num_undef) {
            cout << "WOW Num undef:" << num_undef << endl;
        }

        //Try not to be crazy, 2**30 solutions is enough
        if (num_undef <= 30) {
            solutions += 1U << num_undef;
        } else {
            solutions += 1U << 30;
            cout << "WARNING, in this cut there are > 2**30 solutions indicated by the solver!" << endl;
        }
    }
    if (solutions > maxSolutions) {
        solutions = maxSolutions;
    }

    //Remove clauses added
    vector<Lit> cl_that_removes;
    cl_that_removes.push_back(Lit(act_var, false));
    solver->add_clause(cl_that_removes);

    //Timeout
    if (ret == l_Undef) {
        must_interrupt.store(false, std::memory_order_relaxed);
        return -1;
    }
    return solutions;
}

bool CUSP::ApproxMC(SATCount& count)
{
    count.clear();
    int64_t currentNumSolutions = 0;
    vector<uint64_t> numHashList;
    vector<int64_t> numCountList;
    vector<Lit> assumps;
    for (uint32_t j = 0; j < tApproxMC; j++) {
        uint64_t hashCount;
        uint32_t repeatTry = 0;
        for (hashCount = 0; hashCount < solver->nVars(); hashCount++) {
            cout << "-> Hash Count " << hashCount << endl;
            double myTime = cpuTimeTotal();
            currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps);

            //cout << currentNumSolutions << ", " << pivotApproxMC << endl;
            cusp_logf << "ApproxMC:" << searchMode << ":"
                      << j << ":" << hashCount << ":"
                      << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                      << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                      << currentNumSolutions << endl;
            //Timeout!
            if (currentNumSolutions < 0) {
                //Remove all hashes
                assumps.clear();

                if (repeatTry < 2) {    /* Retry up to twice more */
                    assert(hashCount > 0);
                    AddHash(hashCount, assumps); //add new set of hashes
                    solver->simplify(&assumps);
                    hashCount --;
                    repeatTry += 1;
                    cout << "Timeout, try again -- " << repeatTry << endl;
                } else {
                    //this set of hashes does not work, go up
                    AddHash(hashCount + 1, assumps);
                    solver->simplify(&assumps);
                    cout << "Timeout, moving up" << endl;
                }
                continue;
            }

            if (currentNumSolutions < pivotApproxMC + 1) {
                //less than pivotApproxMC solutions
                break;
            }

            //Found all solutions needed
            AddHash(1, assumps);
        }
        assumps.clear();
        numHashList.push_back(hashCount);
        numCountList.push_back(currentNumSolutions);
        solver->simplify(&assumps);
    }
    if (numHashList.size() == 0) {
        //UNSAT
        return true;
    }

    auto minHash = findMin(numHashList);
    auto hash_it = numHashList.begin();
    auto cnt_it = numCountList.begin();
    for (; hash_it != numHashList.end() && cnt_it != numCountList.end()
            ; hash_it++, cnt_it++
        ) {
        *cnt_it *= pow(2, (*hash_it) - minHash);
    }
    int medSolCount = findMedian(numCountList);

    count.cellSolCount = medSolCount;
    count.hashCount = minHash;
    return true;
}

int CUSP::solve()
{
    conf.reconfigure_at = 0;
    conf.reconfigure_val = 15;
    conf.gaussconf.max_matrix_rows = 3000;
    conf.gaussconf.decision_until = 3000;
    conf.gaussconf.max_num_matrixes = 1;
    conf.gaussconf.min_matrix_rows = 5;
    conf.gaussconf.autodisable = false;

    //set seed
    assert(vm.count("random"));
    unsigned int seed = vm["random"].as<unsigned int>();
    randomEngine.seed(seed);

    openLogFile();
    startTime = cpuTimeTotal();

    solver = new SATSolver((void*)&conf, &must_interrupt);
    solverToInterrupt = solver;
    if (dratf) {
        cout
                << "ERROR: Gauss does NOT work with DRAT and Gauss is needed for CUSP. Exiting."
                << endl;
        exit(-1);
    }
    //check_num_threads_sanity(num_threads);
    //solver->set_num_threads(num_threads);
    if (unset_vars) {
        solver->set_greedy_undef();
    }
    printVersionInfo();
    parseInAllFiles(solver);

    if (startIteration > independent_vars.size()) {
        cout << "ERROR: Manually-specified startIteration"
             "is larger than the size of the independent set.\n" << endl;
        return -1;
    }

    SATCount solCount;
    cout << "Using start iteration " << startIteration << endl;

    bool finished = false;
    if (searchMode == 0) {
        finished = ApproxMC(solCount);
    } else if(searchMode == 1) {
        finished = ScalApproxMC(solCount);
    } else {
        finished = SearchMC(solCount);
    }
    if (searchMode == 0 || searchMode == 1) {
        
        cout << "ApproxMC finished in " << (cpuTimeTotal() - startTime) << " s" << endl;
        if (!finished) {
            cout << " (TIMED OUT)" << endl;
            return 0;
        }

        if (solCount.hashCount == 0 && solCount.cellSolCount == 0) {
            cout << "The input formula is unsatisfiable." << endl;
            return correctReturnValue(l_False);
        }

        if (conf.verbosity) {
            solver->print_stats();
        }

        cout << "Number of solutions is: " << solCount.cellSolCount << " x 2^" << solCount.hashCount << endl;
    } else {
        cout << "SearchMC finished in " << (cpuTimeTotal() - startTime) << " s" << endl;
    }
             

    return correctReturnValue(l_True);
}

int main(int argc, char** argv)
{
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    #ifndef USE_GAUSS
    std::cerr << "CUSP only makes any sese to run if you have configured with:" << endl
              << "*** cmake -DUSE_GAUSS=ON (.. or .)  ***" << endl
              << "Refusing to run. Please reconfigure and then re-compile." << endl;
    exit(-1);
    #else

    CUSP main(argc, argv);
    main.conf.verbStats = 1;
    main.parseCommandLine();
    return main.solve();
    #endif
}

void CUSP::call_after_parse()
{
    if (independent_vars.empty()) {
        cout
        << "c WARNING! No independent vars were set using 'c ind var1 [var2 var3 ..] 0'"
        "notation in the CNF." << endl
        << " c ScalMC may work substantially worse!" << endl;
        for (size_t i = 0; i < solver->nVars(); i++) {
            independent_vars.push_back(i);
        }
    }
    solver->set_independent_vars(&independent_vars);
}

//For ScalApproxMC only
void CUSP::SetHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, vector<Lit>& assumps)
{
    if (clausNum < assumps.size()) {
        uint64_t numberToRemove = assumps.size()- clausNum;
        for (uint64_t i = 0; i<numberToRemove; i++) {
            assumps.pop_back();
        }
    } else {
        if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
            for (uint32_t i = assumps.size(); i< hashVars.size() && i < clausNum; i++) {
                assumps.push_back(hashVars[i]);
            }
        }
        if (clausNum > hashVars.size()) {
            AddHash(clausNum-hashVars.size(),assumps);
            for (uint64_t i = hashVars.size(); i < clausNum; i++) {
                hashVars[i] = assumps[i];
            }
        }
    }
}

//For ScalApproxMC only
bool CUSP::ScalApproxMC(SATCount& count)
{
    count.clear();
    vector<uint64_t> numHashList;
    vector<int64_t> numCountList;
    vector<Lit> assumps;

    uint64_t hashCount = startIteration;
    uint64_t hashPrev = 0;
    uint64_t mPrev = 0;

    double myTime = cpuTimeTotal();
    if (hashCount == 0) {
        int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC+1,assumps);
        cusp_logf << "ApproxMC:"<< searchMode<<":"<<"0:0:"
                  << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                  << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                  << currentNumSolutions << endl;

        //Din't find at least pivotApproxMC+1
        if (currentNumSolutions <= pivotApproxMC) {
            count.cellSolCount = currentNumSolutions;
            count.hashCount = 0;
            return true;
        }
        hashCount++;
    }

    for (uint32_t j = 0; j < tApproxMC; j++) {
        map<uint64_t,int64_t> countRecord;
        map<uint64_t,uint32_t> succRecord;
        map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

        uint32_t repeatTry = 0;
        uint64_t numExplored = 1;
        uint64_t lowerFib = 0, upperFib = independent_vars.size();

        while (numExplored < independent_vars.size()) {
            cout << "Num Explored: " << numExplored
                 << " ind set size: " << independent_vars.size() << endl;
            myTime = cpuTimeTotal();
            uint64_t swapVar = hashCount;
            SetHash(hashCount,hashVars,assumps);
            cout << "Number of XOR hashes active: " << hashCount << endl;
            int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps);

            //cout << currentNumSolutions << ", " << pivotApproxMC << endl;
            cusp_logf << "ApproxMC:" << searchMode<<":"
                      << j << ":" << hashCount << ":"
                      << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                      << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                      << currentNumSolutions << endl;
            //Timeout!
            if (currentNumSolutions < 0) {
                //Remove all hashes
                assumps.clear();
                hashVars.clear();

                if (repeatTry < 2) {    /* Retry up to twice more */
                    assert(hashCount > 0);
                    SetHash(hashCount,hashVars,assumps);
                    solver->simplify(&assumps);
                    hashCount --;
                    repeatTry += 1;
                    cout << "Timeout, try again -- " << repeatTry << endl;
                } else {
                    //this set of hashes does not work, go up
                    SetHash(hashCount + 1, hashVars, assumps);
                    solver->simplify(&assumps);
                    cout << "Timeout, moving up" << endl;
                }
                hashCount = swapVar;
                continue;
            }

            if (currentNumSolutions < pivotApproxMC + 1) {
                numExplored = lowerFib+independent_vars.size()-hashCount;
                if (succRecord.find(hashCount-1) != succRecord.end()
                    && succRecord[hashCount-1] == 1
                ) {
                    numHashList.push_back(hashCount);
                    numCountList.push_back(currentNumSolutions);
                    mPrev = hashCount;
                    //less than pivotApproxMC solutions
                    break;
                }
                succRecord[hashCount] = 0;
                countRecord[hashCount] = currentNumSolutions;
                if (abs(hashCount-mPrev) <= 2 && mPrev != 0) {
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
                assert(currentNumSolutions == pivotApproxMC+1);

                numExplored = hashCount + independent_vars.size()-upperFib;
                if (succRecord.find(hashCount+1) != succRecord.end()
                    && succRecord[hashCount+1] == 0
                ) {
                    numHashList.push_back(hashCount+1);
                    numCountList.push_back(countRecord[hashCount+1]);
                    mPrev = hashCount+1;
                    break;
                }
                succRecord[hashCount] = 1;
                if (abs(hashCount - mPrev) < 2 && mPrev!=0) {
                    lowerFib = hashCount;
                    hashCount ++;
                } else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
                    lowerFib = hashCount;
                    hashCount = (lowerFib+upperFib)/2;
                } else {
                    //printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
                    hashCount = lowerFib + (hashCount -lowerFib)*2;
                }
            }
            hashPrev = swapVar;
        }
        assumps.clear();
        solver->simplify(&assumps);
        hashCount =mPrev;
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

//For SearchMC only
bool CUSP::SearchMC(SATCount& count)
{
    count.clear();
    //vector<uint64_t> numHashList;
    //vector<int64_t> numCountList;
    vector<Lit> assumps;

    double max_w = 64;
    double mu = max_w / 2;
    double sigma = 1000;
    double delta = max_w;
    
    double mu_prime = mu;
    double sigma_prime = sigma;
    double ub = max_w;
    double lb = 0;
    
    int k = mu;
    int exhaust_cnt = 0;
    int sat_cnt = 0;
    uint64_t c = 1;
    
    while (delta > thres) {
        c = ceil(pow((pow(2,sigma)+1)/(pow(2,sigma)-1),2));
        k = floor(mu - log2(double(c))/2);
        if (k < 0) {
            k = 0;
            c = pow(2,independent_vars.size())+1;
        }
        map<uint64_t,Lit> hashVars; //map assumption var to XOR hash
        SetHash(int64_t(k),hashVars,assumps);
        int64_t currentNumSolutions = BoundedSATCount(c, assumps);
        exhaust_cnt++;
        if(currentNumSolutions == int64_t(c)) {
            sat_cnt=sat_cnt+currentNumSolutions;
        } else {
            sat_cnt=sat_cnt+currentNumSolutions+1;
        }
         
        if (k == 0) {
            cout << "Result: Exact # of solutions = " << currentNumSolutions << endl;
        }
        updateDist(&mu_prime, &sigma_prime, mu, sigma, c, k, currentNumSolutions );
        trunc_norm_conf_interval(mu_prime, sigma_prime, 64, cl, &lb, &ub);
        
        cout << exhaust_cnt << ": Old Mu = " << mu << ", Old Sigma = " << sigma << ", nSat = " << currentNumSolutions << ", k = " << k << ", c = " << c << endl;
        cout << exhaust_cnt << ": New Mu = " << mu_prime << ", New Sigma = " << sigma_prime << endl;
        cout << exhaust_cnt << ": Lower Bound = " << lb << ", Upper Bound = " << ub << endl;
        
        mu = mu_prime;
        sigma = sigma_prime;
        delta = ub - lb;
        assumps.clear();
        solver->simplify(&assumps);
    }

    return true;
}

double log_fact(double n) {
    return lgamma(n + 1);
}

/* This algorithm is constant time, but it doesn't work well when n >>
   k, because then log_fact(n) and log_fact(n - k) are too close
   together */
double log_choose_gamma(double n, double k) {
    return (log_fact(n) - log_fact(n - k)) - log_fact(k);
}

/* When n >> k, n!/(n-k)! is almost n^k, which suggests the following
   refinement of log_choose_gamma. However some more thought is
   probably needed about how to choose between the two formulas. */
double log_choose_gamma2(double n, double k) {
    if (n / k > 1000000000) {
        return log(n)*k - log_fact(k);
    } else {
        return (log_fact(n) - log_fact(n - k)) - log_fact(k);
    }
}

/* This algorithm takes O(k) steps, but as long as k is small, it
   gives good results even for very large n.
*/
double log_choose_small_k(double n, uint64_t k) {
    double l = 0;
    uint64_t i;
    for (i = 0; i < k; i++) {
        l += log(n - double(i));
        l -= log(int(k - i));
    }
    return l;
}

#define log_choose log_choose_small_k

#define MAX_INFL 64
#define SAMPLES_PER_BIT 10
#define SAMPLES_PER_BITF ((double)SAMPLES_PER_BIT)
#define NUM_SAMPLES (SAMPLES_PER_BIT*MAX_INFL)
#define NUM_SAMPLESF ((double)SAMPLES_PER_BIT*MAX_INFL)

double prior[NUM_SAMPLES];
double posterior[NUM_SAMPLES];
double fit[NUM_SAMPLES];

void normalize(double *ary, int size) {
    int i;
    double total = 0, new_total = 0;
    for (i = 0; i < size; i++) {
        assert(ary[i] >= 0);
        total += ary[i];
    }
    assert(total > 0);
    for (i = 0; i < size; i++) {
        ary[i] /= total;
        assert(ary[i] >= 0 && ary[i] <= 1.0);
        new_total += ary[i];
    }
    assert(new_total >= 0.999 && new_total <= 1.001);
}

double mean_pdf(double *ary) {
    int i;
    double total = 0;
    for (i = 0; i < NUM_SAMPLES; i++) {
        double x = i/SAMPLES_PER_BITF;
        total += x*ary[i];
    }
    return total;
}

double variance_pdf(double *ary) {
    int i;
    double total_x = 0, total_xx = 0;
    for (i = 0; i < NUM_SAMPLES; i++) {
        double x = i/SAMPLES_PER_BITF;
        total_x += x*ary[i];
        total_xx += x*x*ary[i];
    }
    return total_xx - total_x*total_x;
}

double stddev_pdf(double *ary) {
    return sqrt(variance_pdf(ary));
}

double prob_eq_n(int bt, int k, uint64_t n) {
    double b = (double)bt / SAMPLES_PER_BITF;
    double s = floor(pow(2.0, b) + 0.5);
    double log_p1, log_p2, log_p, p;
    if (n > s)
    	return 0;
    log_p1 = -k * log(2);
    if (k == 0) {
        p = (s == double(n)) ? 1.0 : 0.0;
    } else {
        log_p2 = log1p(-pow(2.0, -k));
        log_p = log_choose(s, n) + log_p1 * n + log_p2 * (s - double(n));
        p = exp(log_p);
    }
    if (p < 0.0) {
        fprintf(stderr, "Bug: negative probability\n");
        exit(1);
    } else if (p > 1.0) {
        fprintf(stderr, "Bug: probability more than 1.0\n");
        fprintf(stderr, "b = %g, k = %d, n = %lu, s = %g\n", b, k, n, s);
        fprintf(stderr, "p = %g\n", p);
        if (n == 1) {
            fprintf(stderr, "log_choose = %g, s/b %g\n",
            log_choose(s, n), log(s));
        }
        exit(1);
    }
    assert(p >= 0.0 && p <= 1.0);
    return p;
}

double prob_ge_n(int bt, int k, uint64_t n) {
    uint64_t n2;
    double prob = 0.0;
    for (n2 = 0; n2 < n; n2++) {
        prob += prob_eq_n(bt, k, n2);
    }
    assert(prob >= -0.0001 && prob <= 1.0001);
    if (prob < 0)
        prob = 0.0;
    if (prob > 1)
        prob = 1.0;
    return 1.0 - prob;
}

void setup_prior_uniform(void) {
    int i;
    for (i = 0; i < NUM_SAMPLES; i++) {
        prior[i] = 1.0;
    }
    normalize(prior, NUM_SAMPLES);
}

void setup_normal(double *ary, double mu, double sigma) {
    int i;
    double denom = 2 * sigma * sigma;
    assert(denom > 0.0);
    for (i = 0; i < NUM_SAMPLES; i++) {
		double x = i/SAMPLES_PER_BITF;
		double diff = x - mu;
		double p = exp(-(diff*diff)/denom);
		assert(p >= 0.0 && p <= 1.0);
		ary[i] = p;
    }
    normalize(ary, NUM_SAMPLES);
}

void estimate_posterior_eq_n(int k, uint64_t n) {
    int bt;
    for (bt = 0; bt < NUM_SAMPLES; bt++) {
		double p = prior[bt]*prob_eq_n(bt, k, n);
		posterior[bt] = p;
    }
    normalize(posterior, NUM_SAMPLES);
}

void estimate_posterior_ge_n(int k, uint64_t n) {
    int bt;
    for (bt = 0; bt < NUM_SAMPLES; bt++) {
		double p = prior[bt]*prob_ge_n(bt, k, n);
		posterior[bt] = p;
    }
    normalize(posterior, NUM_SAMPLES);
}

double calculate_error(double *a1, double *a2) {
    int i;
    double error = 0;
    for (i = 0; i < NUM_SAMPLES; i++) {
        double diff = a1[i] - a2[i];
        error += diff*diff;
    }
    return error;
}

double norm_cdf(double x) {
    return 0.5*erfc(-x/sqrt(2));
}

double norm_inv_cdf(double p) {
    return r8_normal_01_cdf_inverse(p);
}

void CUSP::trunc_norm_conf_interval(double mu, double sigma, double bound, double cl, double *lowerp, double *upperp) {
    double denom1 = sqrt(2)*sigma;
    double integral = 0.5*(erf((bound - mu)/denom1) - erf(-mu/denom1));
    double norm = 1/integral;
    double ci_factor = norm_inv_cdf((cl/norm + 1)/2);
    double ci_sigma = ci_factor * sigma;

    double normal_upper = mu + ci_sigma;
    double normal_lower = mu - ci_sigma;

    double modif_upper = mu + sigma*norm_inv_cdf(cl/norm + norm_cdf(-mu/sigma));
    double modif_lower = mu + sigma*norm_inv_cdf(norm_cdf((bound-mu)/sigma) - cl/norm);

    double upper, lower;
    if (cl == 1.0) {
        upper = bound;
        lower = 0;
    } else if (mu > bound/2.0 && mu <= bound) {
        if (normal_upper <= bound) {
            upper = normal_upper;
            lower = normal_lower;
        } else {
            upper = bound;
            lower = modif_lower;
        }
    } else if (mu <= bound/2.0 && mu >= 0) {
        if (normal_lower >= 0) {
            upper = normal_upper;
            lower = normal_lower;
        } else {
            upper = modif_upper;
            lower = 0;
        }
    } else if (mu > bound) {
        upper = bound;
        lower = modif_lower;
    } else {
        assert(mu < 0);
        upper = modif_upper;
        lower = 0;
    }
    assert(lower >= 0 && lower <= bound);
    assert(upper >= 0 && upper <= bound);
    assert(lower <= upper);
    *lowerp = lower;
    *upperp = upper;
}

double sum_pdf(double *ary, double min, double max) {
    int start = floor(min * SAMPLES_PER_BIT);
    int end = ceil(max * SAMPLES_PER_BIT);
    double sum = 0;
    int i;
    assert(min <= max);
    assert(start <= end);
    for (i = start; i <= end; i++) {
	sum += ary[i];
    }
    if (sum < 0 || sum >= 1.01) {
		for (i = 0; i < NUM_SAMPLES; i++) {
			printf ("%f ", posterior[i]);
		}
		putchar('\n');
		printf ("%f %f error sum: %f\n",min, max, sum);
	}
    assert(sum >= 0 && sum < 1.01);
    return sum;
}

void CUSP::updateDist(double *mu_prime, double *sigma_prime, double mu, double sigma, uint64_t c, int k, uint64_t currentNumSolutions) {
    if (sigma > 100) {
        setup_prior_uniform();
    } else {
        setup_normal(prior, mu, sigma);
    }

    if (c == currentNumSolutions) {
        estimate_posterior_ge_n(k, currentNumSolutions);        
    } else {
        estimate_posterior_eq_n(k, currentNumSolutions);
    }

    double dist = 2;
    double best_mu = -1;
    double best_sigma = HUGE_VAL;
    double best_error = HUGE_VAL;
    double i, j;
    double min_mu = mean_pdf(posterior) - dist;
    double max_mu = mean_pdf(posterior) + dist;
    double min_sigma = stddev_pdf(posterior);
    double max_sigma = stddev_pdf(posterior) + dist;
    
    if (min_mu < 0) {
        min_mu = 0;
    }
    if (min_sigma < 0.01) {
        min_sigma = 0.01;
    }

    for (i = min_mu; i <= max_mu; i += 0.01) {	
        for (j = min_sigma; j < max_sigma; j += 0.01) {
            int cl_i;
            int is_good = 1;
            for (cl_i = 1; cl_i < 100; cl_i++) {
                double norm_lower, norm_upper;
                double cl = cl_i/100.0;
                double post_sum;
                trunc_norm_conf_interval(i, j, 64, cl, &norm_lower, &norm_upper);
                post_sum = sum_pdf(posterior, norm_lower, norm_upper);
                if (cl > post_sum) {
                    is_good = 0;
                    break;
                }
            }
            if (is_good)
                break;
            else if (j > best_sigma)
                break;
        }
    
        if (j <= best_sigma) {
            double error;
            setup_normal(fit, best_mu, best_sigma);
            error = calculate_error(posterior, fit);
            if (j < best_sigma || error < best_error) {
                best_sigma = j;
                best_mu = i;
                best_error = error;
            }
        }
    }

    *mu_prime = best_mu;
    *sigma_prime = best_sigma;
    
    return;
}
