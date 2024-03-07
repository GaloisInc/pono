
#include "mus.h"

#include <smt/available_solvers.h>
#include "utils/logger.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
    // TODO - what does `full_model` do?
    boolector = create_solver_for(BTOR, BMC,false, true);
    toBoolectorInternal = new TermTranslator(boolector);
  }

  Mus::~Mus() {
    controlVars.clear();
    controlTerms.clear();
  }

  ProverResult Mus::check_until(int k)
  {
    Master m(buildMusQuery(k));
    m.enumerate();
    for (int i = 0; i < m.muses.size(); i++) {
      logger.log(0, "MUS #{}", i + 1);
      for(auto &t: musAsOrigTerms(m.muses.at(i))) {
        logger.log(0, "  {}", t);
      }
    }
    return ProverResult::TRUE;
  }

  std::vector<MUS> Mus::check_until_yielding_muses(int k)
  {
    Master m(buildMusQuery(k));
    m.enumerate();
    return m.muses;
  }

  smt::Term Mus::unrollOrigTerm(Term t, int i)
  {
    return toBoolectorInternal->transfer_term(unroller_.at_time(t, i));
  }

  Term Mus::makeControlVar(string id)
  {
    Sort boolSort = boolector->make_sort(SortKind::BOOL);
    Term cv = boolector->make_symbol(id, boolSort);
    controlVars.push_back(cv);
    return cv;
  }

  Term Mus::makeControlVar(ConstraintType type)
  {
    return makeControlVar(constraintTypeToStr[type]);
  }

  Term Mus::makeControlVar(ConstraintType type, const Term t)
  {
    return makeControlVar(constraintTypeToStr[type] + "_" + t->to_string());
  }

  Term Mus::makeControlEquality(const Term& controlVar, const Term& constraint)
  {
    Term eqTerm = boolector->make_term(PrimOp::Equal, controlVar, constraint);
    controlTerms.push_back(eqTerm);
    return eqTerm;
  }

  Master Mus::buildMusQuery(int k)
  {

    if (!options_.logging_smt_solver_) {
      throw invalid_argument("MUS engine requires the --logging-smt-solver flag");
    }

    // TermTranslator toBoolectorInternal(boolector);
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
    if (ts_.is_functional()) {
      for (auto const &su : ts_.state_updates()) {
        Term stateSymbol = su.first;
        Term stateUpdateTerm = solver_->make_term(Equal, ts_.next(stateSymbol), su.second);
        TermVec uts;
        for (int i = 1; i <= k; i++) {
          uts.push_back(unrollOrigTerm(stateUpdateTerm, i - 1));
        }
        transConjuncts.insert({stateSymbol, boolector->make_term(PrimOp::And, uts)});
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
        if (_transConjuncts.find(c) != _transConjuncts.end()) {
          _transConjuncts.erase(c);
          _transConjuncts.erase(solver_->substitute(c, nextMap));
        }
      }

      for (auto &tc: _transConjuncts) {
        TermVec uts;
        for (int i = 1; i <= k; i++) {
          uts.push_back(unrollOrigTerm(tc, i - 1));
        }
        transConjuncts.insert({tc, boolector->make_term(PrimOp::And, uts)});
      }
    }

    for (auto &ic: initConjuncts) {
      Term cv = makeControlVar(ConstraintType::INIT, ic);
      makeControlEquality(cv, unrollOrigTerm(ic, 0));
    }

    for (auto &tc: transConjuncts) {
      Term cv = makeControlVar(ConstraintType::TRANS, tc.first);
      makeControlEquality(cv, tc.second);
    }

    // INVAR
    for(auto &c: ts_.constraints()) {
      TermVec uts;
      for (int i = 0; i <= k; i++) {
        uts.push_back(unrollOrigTerm(c.first, i));
      }
      Term cv = makeControlVar(ConstraintType::INVAR, c.first);
      makeControlEquality(cv, boolector->make_term(PrimOp::And, uts));
    }

    // SPEC
    Term specTerm = boolector->make_term(true);
    for (int i = 0; i <= k; i++) {
      specTerm = boolector->make_term(BVAnd, specTerm, unrollOrigTerm(orig_property_.prop(), i));
    }
    Term specCv = makeControlVar(ConstraintType::SPEC);
    Term negSpec = boolector->make_term(PrimOp::Not, specTerm);
    makeControlEquality(specCv, negSpec);

    // CONTROL TERMS
    Term ctCv = makeControlVar(ConstraintType::CONTROL_TERMS);
    boolector->assert_formula(makeControlEquality(ctCv, boolector->make_term(BVAnd, controlTerms)));

    for(auto &cv: controlVars) {
      boolector->assert_formula(cv);
    }

    string musQueryFile = ".musquery.smt2";
    string musOutputFile = ".muses.smt2";

    boolector->dump_smt2(musQueryFile);

    // MUST defaults to remus when alg isn't specified on CLI
    Master m(musQueryFile, "remus");
    m.output_file = musOutputFile;

    return m;
  }

  TermVec Mus::musAsOrigTerms(MUS mus)
  {
    TermVec terms;
    for(int j = 1; j < mus.bool_mus.size() - 2; j++) {
      if (mus.bool_mus[j]) {
        terms.push_back(controlVars.at(j - 1));
      }
    }
    return terms;
  }

}  // namespace pono
