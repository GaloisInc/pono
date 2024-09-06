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

const string HWMCC = std::string(getenv("QUIIP_MODELS_ROOT")) + "/vectors/hwmcc";

vector<string> getBenchmarks()
{
  const vector<string> testVectors = {
    // == Bit Vector ==
    "anderson.3.prop1-back-serstep.btor2",
    "brp2.2.prop1-func-interl.btor2",
    "elevator.4.prop1-func-interl.btor2",
    "mcs.3.prop1-back-serstep.btor2",
    "pgm_protocol.3.prop5-func-interl.btor2",
    "at.6.prop1-back-serstep.btor2",
    "brp2.3.prop1-back-serstep.btor2",
    "frogs.5.prop1-func-interl.btor2",
    "msmie.3.prop1-func-interl.btor2",
    "pgm_protocol.7.prop1-back-serstep.btor2",
    "blocks.4.prop1-back-serstep.btor2",
    "brp2.6.prop3-back-serstep.btor2",
    "krebs.3.prop1-func-interl.btor2",
    // DISABLED - very slow for bound > 2
    // "peg_solitaire.3.prop1-back-serstep.btor2",
    "rushhour.4.prop1-func-interl.btor2",
    "paper_v3.btor2",
    "h_RCU.btor2",
    "h_TreeArb.btor2",
    "miim.btor2",
    "vcegar_arrays_itc99_b12_p2.btor2",
    "vcegar_QF_BV_ar.btor2",
    "vcegar_QF_BV_itc99_b13_p10.btor2",
    "vis_arrays_am2901.btor2",
    "vis_arrays_am2910_p1.btor2",
    "vis_arrays_am2910_p2.btor2",
    "vis_arrays_am2910_p3.btor2",
    "vis_arrays_buf_bug.btor2",
    "vis_arrays_bufferAlloc.btor2",
    "intersymbol_analog_estimation_convergence.btor",
    // DISABLED - slow
    // "ridecore.btor",
    // DISABLED - slow
    // "buggy_ridecore.btor",
    "marlann_compute_cp_fail1-p2.btor",
    "marlann_compute_cp_fail2-p0.btor",
    "marlann_compute_cp_pass-p2.btor",
    "rast-p00.btor",
    "rast-p03.btor",
    "rast-p06.btor",
    "rast-p14.btor",
    "rast-p17.btor",
    "rast-p19.btor",
    "simple_alu.btor",
    "stack-p2.btor",
    "rast-p01.btor",
    "rast-p04.btor",
    "rast-p11.btor",
    "rast-p16.btor",
    "rast-p18.btor",
    "rast-p21.btor",
    "stack-p1.btor",

    // == Array ==
    "arbitrated_fifos_n2d8w8.btor",
    "array_swap.btor",
    "easy_zero_array.btor",
    "simple-stack-pred1.btor"
  };
  vector<string> benchmarks;
  for (const auto & testVector: testVectors) {
    benchmarks.push_back(HWMCC + "/" + testVector);
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
