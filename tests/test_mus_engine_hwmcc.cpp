#include <engines/bmc.h>
#include <engines/mus.h>
#include <modifiers/prop_monitor.h>

#include <string>
#include <tuple>
#include <vector>
#include <filesystem>

#include "core/fts.h"
#include "frontends/btor2_encoder.h"
#include "gtest/gtest.h"
#include "smt-switch/logging_solver.h"
#include "smt/available_solvers.h"

using namespace pono;
using namespace smt;
using namespace std;

namespace fs = std::filesystem;

namespace pono_tests {

class MusEngineSameSatResult : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int>>
{
};

const string HWMCC = getenv("HWMCC_ROOT");

vector<string> getBenchmarks()
{
  const vector<string> testDirs = {
    // = Bit Vector =
    "bv/2019/beem",
    "bv/2019/goel/crafted",
    "bv/2019/goel/opensource",
    // "bv/2019/goel/industry", // Very slow due to use of large bitvectors
    "bv/2019/wolf/2019B",
    "bv/2019/mann/safe",
    "bv/2019/mann/unknown",
    "bv/2019/mann/unsafe",
    "bv/2020/mann",

    // = Array =
    "array/2019/mann/safe",
    //
    // "array/2019/mann/unsafe",
    // "array/2019/mann/unknown",
    // "array/2019/wolf/2019B",
    "array/2020/mann"
  };
  const vector<string> ignore = {

    // very slow for bound > 2
    HWMCC + "bv/2019/beem/peg_solitaire.3.prop1-back-serstep.btor2",

    // slow
    HWMCC + "bv/2019/mann/unknown/ridecore.btor",
    HWMCC + "bv/2019/mann/unsafe/buggy_ridecore.btor",
  };
  vector<string> benchmarks;
  for (const auto & testDir: testDirs) {
    for (const auto & entry : std::filesystem::recursive_directory_iterator(fs::path(HWMCC + testDir))) {
      if (entry.is_regular_file()) {
        if (std::find(ignore.begin(), ignore.end(), entry.path().string()) == ignore.end()) {
          benchmarks.push_back(entry.path());
        }
      }
    }
  }
  return benchmarks;
}

TEST_P(MusEngineSameSatResult, benchmarks)
{
  auto makeSolver = [] {
    SmtSolver s = make_shared<LoggingSolver>(create_solver(SolverEnum::BTOR));
    FunctionalTransitionSystem fts(s);
    BTOR2Encoder be(get<0>(GetParam()), fts);
    EXPECT_EQ(be.propvec().size(), 1);
    Term pTerm = be.propvec()[0];
    if (!fts.only_curr(pTerm)) {
      pTerm = add_prop_monitor(fts, pTerm);
    }
    Property p(fts.solver(), pTerm);
    return tuple(p, fts, s);
  };

  int bound = get<1>(GetParam());

  tuple<Property, FunctionalTransitionSystem, SmtSolver> tMus = makeSolver();
  PonoOptions opts = PonoOptions();
  opts.mus_atomic_init_ = true;
  Mus mus(get<0>(tMus), get<1>(tMus), get<2>(tMus), opts);
  Master must(mus.buildMusQuery(bound));

  tuple<Property, FunctionalTransitionSystem, SmtSolver> tBmc = makeSolver();
  Bmc bmc(get<0>(tBmc), get<1>(tBmc), get<2>(tBmc));

  ProverResult bmcResult = bmc.check_until(bound);

  Formula whole(must.dimension, true);
  bool mustSatResult = must.is_valid(whole);

  if (bmcResult == ProverResult::UNKNOWN) {
    EXPECT_FALSE(mustSatResult);
  } else if (bmcResult == ProverResult::FALSE)  {
    EXPECT_TRUE(mustSatResult);
  } else {
    assert(false);
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineSameSatResult,
    testing::Combine(
      testing::ValuesIn(getBenchmarks()),
      testing::ValuesIn({2, 5}))
    );

}  // namespace pono_tests
