
#include "mus.h"
#include "smt/available_solvers.h"
#include <regex>
#include "utils/logger.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
  }

  Mus::~Mus() {
    controlVars.clear();
  }

  // TODO(rperoutka) - Master.enumerate `exit(1)`s on satisfiable instances.
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

  Term Mus::unrollUntilBound(Term t, int k)
  {
    TermVec uts;
    for (int i = 0; i < k; i++) {
      uts.push_back(unroller_.at_time(t, i));
    }
    return makeConjunction(uts);
  }

  Term Mus::makeControlVar(string id)
  {
    Sort boolSort = solver_->make_sort(SortKind::BOOL);
    Term cv = solver_->make_symbol(id, boolSort);
    controlVars.push_back(cv);
    return cv;
  }

  Term Mus::makeControlVar(ConstraintType type)
  {
    return makeControlVar(constraintTypeToStr[type]);
  }

  Term Mus::makeControlVar(ConstraintType type, const Term t)
  {
    string s = t->to_string();
    if (type == INVAR) {
      s = std::to_string(t->hash());
    }
    return makeControlVar(constraintTypeToStr[type] + "_" + s);
  }

  void Mus::assertControlEquality(const Term& controlVar, const Term& constraint)
  {
    solver_->assert_formula(solver_->make_term(PrimOp::Equal, controlVar, constraint));
  }

  Term Mus::makeConjunction(TermVec ts)
  {
    return ts.size() == 1 ? ts[0] : solver_->make_term(PrimOp::And, ts);
  }

  UnorderedTermSet Mus::extractTopLevelConjuncts(Term conjunction)
  {
    UnorderedTermSet conjuncts;
    Term t = conjunction;
    while (t->get_op() == PrimOp::And) {
      TermIter tIter = t->begin();
      t = *tIter;
      Term _init = *++tIter;
      conjuncts.insert(_init);
    }
    if (t != solver_->make_term(true)) {
      conjuncts.insert(t);
    }
    return conjuncts;
  }


  /*
   * Construct a MUST Master object initialized with our MUS query in
   * `SmtSolver` form.
   *
   * The constraint set we set up for MUST to reason over consists of
   *  - `INIT` constraints (top-level conjuncts of TransitionSystem.init())
   *  - `TRANS` constraints (top-level conjuncts of TransitionSystem.trans())
   *  - `INVAR` constraints (elements of TransitionSystem.constraints())
   *  - `SPEC` the negation of the safety property
   *
   * For each element of the constraint set, we introduce a new symbol ("control
   * variable").
   *
   */
  Master Mus::buildMusQuery(int k)
  {

    UnorderedTermSet initConjuncts;
    if (options_.mus_atomic_init_) {
      initConjuncts.insert(ts_.init());
    } else {
      initConjuncts = extractTopLevelConjuncts(ts_.init());
    }

    UnorderedTermSet transConjuncts = extractTopLevelConjuncts(ts_.trans());

    /*
     *  Constraints are populated in the TransitionSystem for SMV `INVAR`s and
     *  BTOR2 `constraint`s. They're automatically added to both the
     *  TransitionSystem's init and trans conjunctions. We'd like to treat these
     *  as atomic constraints in our MUSes.
     */
    UnorderedTermMap nextMap;
    for(auto &v: ts_.statevars()) {
      nextMap.insert({v, ts_.next(v)});
    }
    UnorderedTermSet constraints;
    for (auto & c: ts_.constraints()) {
      assert(c.second);
      constraints.insert(c.first);
    }
    for (auto &c: constraints) {
      initConjuncts.erase(c);
      transConjuncts.erase(c);
      transConjuncts.erase(solver_->substitute(c, nextMap));
    }

    /*
     * If the conjunct encodes a state update constraint (i.e. of form
     * <stateVar>.next = ...), then uses that state variable's id for the
     * control var symbol. Otherwise use the conjunct's to_string as an
     * identifier.
     */
    UnorderedTermMap transIdToConjunct;
    for (auto &tc: transConjuncts) {
      Term id = tc;
      if (tc->get_op() == PrimOp::Equal) {
        Term lhs = *tc->begin();
        if (ts_.is_next_var(lhs)) {
          id = lhs;
        }
      }
      Term t = unrollUntilBound(tc, k);
      if (!options_.mus_include_yosys_internal_netnames_ && id->to_string().rfind('$', 0) == 0) {
        solver_->assert_formula(t);
      } else {
        transIdToConjunct.insert({id, t});
      }
    }

    for (auto &ic: initConjuncts) {
      Term cv;
      if (options_.mus_atomic_init_) {
        assert(initConjuncts.size() == 1);
        cv = makeControlVar(ConstraintType::INIT);
      } else {
        cv = makeControlVar(ConstraintType::INIT, ic);
      }
      assertControlEquality(cv, unroller_.at_time(ic, 0));
    }

    for (auto &tc: transIdToConjunct) {
      Term cv = makeControlVar(ConstraintType::TRANS, tc.first);
      assertControlEquality(cv, tc.second);
    }

    for(auto &c: ts_.constraints()) {
      Term cv = makeControlVar(ConstraintType::INVAR, c.first);
      assertControlEquality(cv, unrollUntilBound(c.first, k + 1));
    }

    Term spec = orig_property_.prop();
    logger.log(0, "Checking Spec: {}", spec);
    Term specCv = makeControlVar(ConstraintType::SPEC, spec);
    Term negSpec = solver_->make_term(PrimOp::Not, unrollUntilBound(spec, k + 1));
    assertControlEquality(specCv, negSpec);

    return Master(solver_, controlVars, "remus");
  }

  /*
   * MUS::bool_mus marks which assertions (in the order they appear in the MUS
   * query) are elements of the MUS.
   */
  TermVec Mus::musAsOrigTerms(MUS mus)
  {
    TermVec terms;
    for (int i = 0; i < controlVars.size(); i++) {
      if (mus.bool_mus[i]) {
        terms.push_back(controlVars[i]);
      }
    }
    return terms;
  }

}  // namespace pono
