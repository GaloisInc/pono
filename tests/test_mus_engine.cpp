#include <engines/mus.h>

#include <string>
#include <tuple>
#include <vector>

#include "core/fts.h"
#include "frontends/btor2_encoder.h"
#include "gtest/gtest.h"
#include "smt/available_solvers.h"

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

const string QUIIP_MODELS = getenv("QUIIP_MODELS_ROOT");

const vector<tuple<string, int, int>> quiip_models_btor2_unsat({
  tuple("test-models-btor2/count2/count2.btor2", 5, 1),
  tuple("test-models-btor2/count2/count2mus.btor2", 5, 2),
});

const vector<tuple<string, int>> quiip_models_btor2_sat({
  tuple("test-models-btor2/count2/count2.btor2", 10),
  tuple("test-models-btor2/count2/count2mus.btor2", 10)
});

const vector<tuple<string, int>> pono_btor2_inputs({
  tuple("counter.btor", 10),
  tuple("counter-true.btor", 10),
  tuple("mem.btor", 10),
  tuple("array_neq.btor2", 10),
  //tuple("ridecore.btor", 10),
  tuple("state2input.btor", 10),
  tuple("WRITE_COUNTER.btor2", 10)
});

TEST_P(MusEngineTestsUnsat, Unsat)
{
  SmtSolver s = create_solver(SolverEnum::BTOR);
  FunctionalTransitionSystem fts(s);
  string filename = QUIIP_MODELS + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Property p(fts.solver(), be.propvec()[0]);
  Mus mus(p, fts, s);
  std::vector<MUS> muses = mus.check_until_yielding_muses(get<1>(GetParam()));
  EXPECT_EQ(muses.size(), get<2>(GetParam()));
}

TEST_P(MusEngineTestsSat, Sat)
{
  SmtSolver s = create_solver(SolverEnum::BTOR);
  FunctionalTransitionSystem fts(s);
  string filename = QUIIP_MODELS + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Property p(fts.solver(), be.propvec()[0]);
  Mus mus(p, fts, s);
  // TODO - MUST `exit(1)`s on satisfiable instances
  auto r = [&mus]() {
    return mus.check_until(get<1>(GetParam()));
  };
  EXPECT_EXIT(r(), ::testing::ExitedWithCode(1), ".*");
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineTestsUnsat,
    testing::ValuesIn(quiip_models_btor2_unsat));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineTestsSat,
    testing::ValuesIn(quiip_models_btor2_sat));

}  // namespace pono_tests
