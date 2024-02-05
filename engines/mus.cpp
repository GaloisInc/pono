
#include "mus.h"
#include <fstream>

#include "Master.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
  }

  Mus::~Mus() {}

  ProverResult Mus::check_until(int k) {

    string fname = ".musQuery.smt2";
    ofstream f;
    f.open(fname);

    auto comment = [&f](string c) {
      f << ";" << c << std::endl;
    };

    auto assert_formula = [&f](Term t) {
      f << "(assert " << t << ")" << std::endl;
    };

    auto declare_const = [&f](Sort s, Term t) {
      f << "(declare-const " << t << " " << s << ")" << std::endl;
    };

    comment("input vars");
    for (auto const & t : ts_.inputvars()) {
      for (int i = 0; i <= k; i++) {
        declare_const(t->get_sort(), unroller_.at_time(t, i));
      }
    }

    comment("state vars");
    for (auto const & t : ts_.statevars()) {
      for (int i = 0; i <= k; i++) {
        declare_const(t->get_sort(), unroller_.at_time(t, i));
      }
    }

    comment("init");
    for (auto const & t : extractTopLevelConjuncts(ts_.init())) {
      assert_formula(unroller_.at_time(t, 0));
    }

    comment("trans");
    for (auto const & t : extractTopLevelConjuncts(ts_.trans())) {
      Term _t = solver_->make_term(true);
      for (int i = 1; i <= k; i++) {
        _t = solver_->make_term(PrimOp::And, _t, unroller_.at_time(t, i - 1));
      }
      assert_formula(_t);
    }

    comment("spec");
    Term _t = solver_->make_term(true);
    for (int i = 0; i <= k; i++) {
      _t = solver_->make_term(PrimOp::And, _t, unroller_.at_time(orig_property_.prop(), i));
    }
    _t = solver_->make_term(PrimOp::Not, _t);
    assert_formula(_t);

    f.close();

    // MUST default to remus when alg isn't specified on CLI
    Master musSolver(fname, "remus");
    // TODO - this `exit(1)`s if it's SAT
    musSolver.enumerate();

    return ProverResult::TRUE;
  }

  smt::UnorderedTermSet Mus::extractTopLevelConjuncts(Term t) {
    std::unordered_set<Term> c;
    Term _t = t;
    // Cvc5 combines top-level conjuncts with `And`s, boolector uses `BVAnd`
    while(_t->get_op() == PrimOp::And || _t->get_op() == PrimOp::BVAnd) {
      TermIter tIter = _t->begin();
      _t = *tIter;
      c.insert(*++tIter);
    }
    c.insert(_t);
    return c;
  }

}  // namespace pono
