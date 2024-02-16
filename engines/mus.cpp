
#include "mus.h"

#include "Master.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
  }

  Mus::~Mus() = default;

  ProverResult Mus::check_until(int k)
  {
    if (!solver_->get_solver_enum() == BTOR) {
      // We rely on boolector's `dump_smt2` being implemented
      throw invalid_argument("MUS engine requires BTOR solver");
    }

    if (options_.logging_smt_solver_) {
      // LoggingSolver's `dump_smt2` does not invoke its wrapped solver's implementation
      throw invalid_argument("MUS engine cannot be used with a Logging Solver");
    }

    assertInitConstraints();
    assertUnrolledTransConstraints(k);
    assertUnrolledSpec(k);

    string musQueryFile = ".musquery.smt2";
    string musOutputFile = ".muses.smt2";

    solver_->dump_smt2(musQueryFile);

    // MUST defaults to remus when alg isn't specified on CLI
    Master musSolver(musQueryFile, "remus");
    musSolver.output_file = musOutputFile;
    // TODO - this `exit(1)`s if it's SAT
    musSolver.enumerate();

    return ProverResult::TRUE;
  }

  void Mus::assertInitConstraints() {
    Term t = ts_.init();
    while(t->get_op() == PrimOp::BVAnd) {
      TermIter tIter = t->begin();
      t = *tIter;
      solver_->assert_formula(unroller_.at_time(*++tIter, 0));
    }
    solver_->assert_formula(unroller_.at_time(t, 0));
  }

  void Mus::assertUnrolledTransConstraints(int k) {
    UnorderedTermSet unrolledTransConjuncts;
    Sort boolSort = solver_->make_sort(SortKind::BOOL);
    for (auto const & stateUpdate : ts_.state_updates()) {
      Term stateSymbol = stateUpdate.first;
      Term tConstraint = solver_->make_term(Equal, ts_.next(stateSymbol), stateUpdate.second);
      Term transSymbol = solver_->make_symbol("t_" + stateSymbol->to_string(), boolSort);
      Term _t = solver_->make_term(true);
      for (int i = 1; i <= k; i++) {
        _t = solver_->make_term(PrimOp::And, _t, unroller_.at_time(tConstraint, i - 1));
      }
      unrolledTransConjuncts.insert(solver_->make_term(Equal, transSymbol, _t));
      solver_->assert_formula(transSymbol);
    }

    Term t = solver_->make_term(true);
    Term transSymbolsConjunction = solver_->make_symbol("_transSymbols", boolSort);
    for (auto const & saveEqT : unrolledTransConjuncts) {
      t = solver_->make_term(And, t, saveEqT);
    }
    solver_->assert_formula(solver_->make_term(Equal, transSymbolsConjunction, t));
    solver_->assert_formula(transSymbolsConjunction);
  }

  void Mus::assertUnrolledSpec(int k) {
    Term t = solver_->make_term(true);
    for (int i = 0; i <= k; i++) {
      t = solver_->make_term(PrimOp::And, t, unroller_.at_time(orig_property_.prop(), i));
    }
    solver_->assert_formula(solver_->make_term(PrimOp::Not, t));
  }

}  // namespace pono
