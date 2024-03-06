
#include "mus.h"

#include <smt/available_solvers.h>

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
    boolectorInternal = create_solver_for(BTOR, BMC,false, true); // TODO - what does `full_model` do?
  }

  Mus::~Mus() = default;

  void Mus::assert_formula(Term t, TermTranslator tt)
  {
    boolectorInternal->assert_formula(tt.transfer_term(t));
  }


  ProverResult Mus::check_until(int k)
  {
    Master m(buildMusQuery(k));
    m.enumerate();
    return ProverResult::TRUE;
  }

  std::vector<MUS> Mus::check_until_yielding_muses(int k)
  {
    Master m(buildMusQuery(k));
    m.enumerate();
    return m.muses;
  }

  Master Mus::buildMusQuery(int k)
  {

    if (!options_.logging_smt_solver_) {
      throw invalid_argument("MUS engine requires the --logging-smt-solver flag");
    }

    TermTranslator toBoolectorInternal(boolectorInternal);
    Term _true = solver_->make_term(true);

    UnorderedTermSet initConjuncts;
    Term init = ts_.init();
    while (init->get_op() == PrimOp::And) {
      TermIter tIter = init->begin();
      init = *tIter;
      Term _init = *++tIter;
      initConjuncts.insert(_init);
    }
    if (init != _true) {
      initConjuncts.insert(init);
    }

    UnorderedTermMap transConjuncts;
    Sort boolSort = boolectorInternal->make_sort(SortKind::BOOL);
    if (ts_.is_functional()) {

      // assert(ts_.constraints().empty());

      // TRANS
      for (auto const &su : ts_.state_updates()) {
        Term stateSymbol = su.first;
        Term stateUpdateTerm = solver_->make_term(Equal, ts_.next(stateSymbol), su.second);
        Term _t = solver_->make_term(true);
        for (int i = 1; i <= k; i++) {
          _t = solver_->make_term(PrimOp::And, _t, unroller_.at_time(stateUpdateTerm, i - 1));
        }

        transConjuncts.insert({boolectorInternal->make_symbol("TRANS_" + stateSymbol->to_string(), boolSort), _t});
      }

    } else {
      UnorderedTermSet constraints;
      for (auto & c: ts_.constraints()) {
        assert(c.second);
        constraints.insert(c.first);
      }

      UnorderedTermSet _transConjuncts;
      Term trans = ts_.trans();
      while (trans->get_op() == PrimOp::And) {
        TermIter tIter = trans->begin();
        trans = *tIter;
        Term _trans = *++tIter;
        _transConjuncts.insert(_trans);
      }
      if (trans != _true) {
        _transConjuncts.insert(trans);
      }


      UnorderedTermMap nextMap;
      for(auto &v: ts_.statevars()) {
        nextMap.insert({v, ts_.next(v)});
      }

      for (auto &c: constraints) {
        if (initConjuncts.find(c) != initConjuncts.end()) {
          initConjuncts.erase(c);
        }
        if (transConjuncts.find(c) != transConjuncts.end()) {
          _transConjuncts.erase(c);
          _transConjuncts.erase(solver_->substitute(c, nextMap));
        }
      }

      for (auto &tc: _transConjuncts) {
        Term _t = solver_->make_term(true);
        for (int i = 1; i <= k; i++) {
          _t = solver_->make_term(PrimOp::And, _t, unroller_.at_time(tc, i - 1));
        }
        transConjuncts.insert({boolectorInternal->make_symbol("TRANS_" + std::to_string(_t->hash()), boolSort), _t});
      }
    }

    UnorderedTermSet controlVars;
    UnorderedTermSet controlTerms;
    // UnorderedTermSet

    for (auto &ic: initConjuncts) {
      Term iSymbol = boolectorInternal->make_symbol("INIT_" + std::to_string(ic->hash()), boolSort);
      controlVars.insert(iSymbol);
      Term iTerm = toBoolectorInternal.transfer_term(unroller_.at_time(ic, 0));
      // controlledTerms.insert(iTerm);
      Term eqTerm = boolectorInternal->make_term(Equal, iSymbol, iTerm);
      controlTerms.insert(eqTerm);
      // boolectorInternal->assert_formula(boolectorInternal->make_term(Equal, iSymbol, iTerm));
      boolectorInternal->assert_formula(iSymbol);
    }

    for (auto &tc: transConjuncts) {
      controlVars.insert(tc.first);
      Term tcSecondBi = toBoolectorInternal.transfer_term(tc.second);
      // controlTerms.insert(tcSecondBi);
      Term eqTerm = boolectorInternal->make_term(Equal, tc.first, tcSecondBi);
      controlTerms.insert(eqTerm);
      // boolectorInternal->assert_formula(eqTerm);
      boolectorInternal->assert_formula(tc.first);
    }

    // INVAR
    for(auto &c: ts_.constraints()) {
      Term invarTerm = boolectorInternal->make_term(true);
      for (int i = 0; i <= k; i++) {
        Term biC = toBoolectorInternal.transfer_term(c.first);
        invarTerm = boolectorInternal->make_term(BVAnd, invarTerm, biC);
      }
      Term invarSymbol = boolectorInternal->make_symbol("INVAR_" + std::to_string(invarTerm->hash()), boolSort);
      controlVars.insert(invarSymbol);
      Term eqTerm = boolectorInternal->make_term(PrimOp::Equal, invarSymbol, invarTerm);
      controlTerms.insert(eqTerm);
    }

    // SPEC
    Term specTerm = boolectorInternal->make_term(true);
    for (int i = 0; i <= k; i++) {
      Term _t = unroller_.at_time(orig_property_.prop(), i);
      specTerm = boolectorInternal->make_term(BVAnd, specTerm, toBoolectorInternal.transfer_term(_t));
    }
    Term specSymbol = boolectorInternal->make_symbol("SPEC", boolSort);
    controlVars.insert(specSymbol);
    Term negSpec = boolectorInternal->make_term(PrimOp::Not, specTerm);
    Term eqTerm = boolectorInternal->make_term(PrimOp::Equal, specSymbol, negSpec);
    controlTerms.insert(eqTerm);
    boolectorInternal->assert_formula(specSymbol);

    // CONTROL TERMS
    Term cTerm = boolectorInternal->make_term(true);
    for(auto &ct: controlTerms) {
      cTerm = boolectorInternal->make_term(BVAnd, ct, cTerm); // TODO - termvec??
    }
    Term controlledTermsSymbol = boolectorInternal->make_symbol("CONTROL_TERMS", boolSort);
    boolectorInternal->assert_formula(boolectorInternal->make_term(Equal, controlledTermsSymbol, cTerm));
    boolectorInternal->assert_formula(controlledTermsSymbol);

    string musQueryFile = ".musquery.smt2";
    string musOutputFile = ".muses.smt2";

    boolectorInternal->dump_smt2(musQueryFile);

    // MUST defaults to remus when alg isn't specified on CLI
    Master m(musQueryFile, "remus");
    m.output_file = musOutputFile;
    return m;
  }

}  // namespace pono
