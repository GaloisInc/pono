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

class MusEngineUnitTests : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int, ProverResult>>
{
};

const string QUIIP_MODELS = getenv("QUIIP_MODELS_ROOT");

const vector<tuple<string, int, ProverResult>> quiip_models_inputs({
  tuple("test-models-btor2/count2/count2.btor2", 5, ProverResult::TRUE),
  tuple("test-models-btor2/count2/count2mus.btor2", 5, ProverResult::TRUE),
  tuple("test-models-btor2/count2/count2.btor2", 10, ProverResult::FALSE),
  tuple("test-models-btor2/count2/count2mus.btor2", 10, ProverResult::FALSE)
});

TEST_P(MusEngineUnitTests, Unsat)
{
  SmtSolver s = create_solver(SolverEnum::BTOR);
  FunctionalTransitionSystem fts(s);
  string filename = QUIIP_MODELS + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Property p(fts.solver(), be.propvec()[0]);
  Mus mus(p, fts, s);
  auto r = [](Mus mus) {
    return mus.check_until(get<1>(GetParam()));
  };
  if (get<2>(GetParam()) == ProverResult::TRUE) {\
    EXPECT_EQ(r(mus), ProverResult::TRUE);
  } else {
    // TODO - MUST `exit(1)`s on satisfiable instances
    EXPECT_EXIT(r(mus), ::testing::ExitedWithCode(1), ".*");
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MusEngineUnitTests,
    testing::ValuesIn(quiip_models_inputs));

}  // namespace pono_tests
