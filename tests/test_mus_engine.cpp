#include <engines/mus.h>

#include <string>
#include <tuple>
#include <vector>

#include "core/fts.h"
#include "core/rts.h"
#include "frontends/btor2_encoder.h"
#include "frontends/smv_encoder.h"
#include "gtest/gtest.h"
#include "smt/available_solvers.h"
#include "smt-switch/logging_solver.h"

using namespace pono;
using namespace smt;
using namespace std;

namespace pono_tests {

class MusEngineTestsUnsat : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int, int>>
{
};

class MusEngineTestsSat : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int>>
{
};

const string QUIIP_MODELS = std::string(getenv("QUIIP_MODELS_ROOT")) + "/vectors";

const vector<tuple<string, int, int>> quiip_models_unsat({
  // BTOR2
  tuple("count2.btor2", 5, 1),
  tuple("count2mus.btor2", 5, 2),
  tuple("example.btor2", 5, 1),
  // SMV
  tuple("altitude_switch_model.smv", 5, 2),
  tuple("simple_counter.smv", 5, 1),
  tuple("count2.smv", 5, 1),
  tuple("count2mus.smv", 5, 2),
  tuple("unreachable_states.smv", 100, 1)
});

const vector<tuple<string, int>> quiip_models_btor2_sat({
  tuple("count2.btor2", 10),
  tuple("count2mus.btor2", 10),
  tuple("example.btor2", 10)
});

TEST_P(MusEngineTestsUnsat, Unsat)
{
  SmtSolver s = make_shared<LoggingSolver>(create_solver(SolverEnum::BTOR));
  string filename = QUIIP_MODELS + "/" + get<0>(GetParam());
  string file_ext = get<0>(GetParam()).substr(get<0>(GetParam()).find_last_of(".") + 1);
  TransitionSystem ts;
  Term prop;
  if (file_ext == "btor" || file_ext == "btor2") {
    ts = FunctionalTransitionSystem(s);
    BTOR2Encoder be(filename, ts);
    EXPECT_EQ(be.propvec().size(), 1);
    prop = be.propvec()[0];
  } else if (file_ext == "smv") {
    RelationalTransitionSystem rts(s);
    SMVEncoder se(filename, rts);
    EXPECT_EQ(se.propvec().size(), 1);
    prop = se.propvec()[0];
    ts = rts;
  }

  Property p(ts.solver(), prop);
  PonoOptions opts = PonoOptions();
  opts.logging_smt_solver_ = true;
  Mus mus(p, ts, s, opts);
  std::vector<MUS> muses = mus.check_until_yielding_muses(get<1>(GetParam()));
  EXPECT_EQ(muses.size(), get<2>(GetParam()));
}

TEST_P(MusEngineTestsSat, Sat)
{
  SmtSolver s = make_shared<LoggingSolver>(create_solver(SolverEnum::BTOR));
  FunctionalTransitionSystem fts(s);
  string filename = QUIIP_MODELS + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Property p(fts.solver(), be.propvec()[0]);
  PonoOptions opts = PonoOptions();
  opts.logging_smt_solver_ = true;
  Mus mus(p, fts, s, opts);
  // TODO - MUST `exit(1)`s on satisfiable instances
  auto r = [&mus]() {
    return mus.check_until(get<1>(GetParam()));
  };
  EXPECT_EXIT(r(), ::testing::ExitedWithCode(1), ".*");
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineTestsUnsat,
    testing::ValuesIn(quiip_models_unsat));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineTestsSat,
    testing::ValuesIn(quiip_models_btor2_sat));

}  // namespace pono_tests
