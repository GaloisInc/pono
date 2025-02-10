#include <engines/mus.h>
#include <modifiers/prop_monitor.h>

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

class MUSTseitinless : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int, int>>
{
};

class MUSWithTseitin : public ::testing::Test,
                       public ::testing::WithParamInterface<tuple<string, int, int>>
{
};

const string SPA_COMB_DIR = std::string(getenv("QUIIP_MODELS_ROOT")) + "/vectors/spa_comb";

const vector<tuple<string, int, int>> spa_comb_btor({
  tuple("verify_spa_comb_simplex.btor", 10, 1/* ??? */),
  tuple("verify_spa_comb_duplex1.btor", 10, 1/* ??? */),
  tuple("verify_spa_comb_duplex2.btor", 10, 1/* ??? */)
});

TEST_P(MUSTseitinless, Sat)
{
  SmtSolver s = make_shared<LoggingSolver>(create_solver(SolverEnum::BTOR));
  FunctionalTransitionSystem fts(s);
  string filename = SPA_COMB_DIR + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Term prop = be.propvec()[0];
  prop = add_prop_monitor(fts, prop);
  Property p(fts.solver(), prop);
  PonoOptions opts = PonoOptions();
  opts.logging_smt_solver_ = true;
  Mus mus(p, fts, s, opts);
  // TODO - MUST `exit(1)`s on satisfiable instances
  auto r = [&mus]() {
    return mus.check_until(get<1>(GetParam()));
  };
  EXPECT_EQ(r(), 1);
}

TEST_P(MUSWithTseitin, Sat)
{
  SmtSolver s = make_shared<LoggingSolver>(create_solver(SolverEnum::BTOR));
  FunctionalTransitionSystem fts(s);
  string filename = SPA_COMB_DIR + "/" + get<0>(GetParam());
  BTOR2Encoder be(filename, fts);
  EXPECT_EQ(be.propvec().size(), 1);
  Term prop = be.propvec()[0];
  prop = add_prop_monitor(fts, prop);
  Property p(fts.solver(), prop);
  PonoOptions opts = PonoOptions();
  opts.logging_smt_solver_ = true;
  opts.mus_apply_tseitin_ = true;
  Mus mus(p, fts, s, opts);
  // TODO - MUST `exit(1)`s on satisfiable instances
  std::vector<MUS> muses = mus.check_until_yielding_muses(get<1>(GetParam()));
  int expected_num_muses = get<2>(GetParam());
  EXPECT_EQ(expected_num_muses, muses.size());
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MUSTseitinless,
    testing::ValuesIn(spa_comb_btor));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverMusUnitTests,
    MUSWithTseitin,
    testing::ValuesIn(spa_comb_btor));

}  // namespace pono_tests
