
#include "mus.h"
#include <smt-switch/boolector_factory.h>
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
    logger.log(1, "= MUS Assertions =");
    for (auto &ma: musAssertions) {
      logger.log(1, "{} <-> {}", ma.first, ma.second);
    }
    logger.log(1, "= Contextual Assertions =");
    for (auto &ca: contextualAssertions) {
      logger.log(1, "{}", ca);
    }
    m.enumerate();
    for (int i = 0; i < m.muses.size(); i++) {
      logger.log(0, "MUS #{}", i + 1);
      for(auto &t: musAsOrigTerms(m.muses.at(i))) {
        logger.log(0, "  {}", t);
      }
    }
    if (tseitinVars.size() != 0) {
      logger.log(0, "= Tseitin Variables =");
      for (auto &tv: tseitinVars) {
        logger.log(0, "{} := {}", tv, tseitinVarToConstraint[tv]);
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

  Term Mus::tseitinDecompose(Term t, int k)
  {
    Op op = t->get_op();
    if (op == NUM_OPS_AND_NULL) {
      // Base case - cannot further decompose atomic terms
      return t;
    }
    TermVec ts;
    TermIter tIter = t->begin();
    if (op == Ite) {
      while (tIter != t->end()) {
        if (tIter == t->begin()) {
          ts.push_back(*tIter);
          *tIter++;
        } else {
          Term tt = tseitinDecompose(*tIter, k);
          ts.push_back(tt);
          *tIter++;
        }
      }
    } else {
      while (tIter != t->end()) {
        Term tt = tseitinDecompose(*tIter, k);
        ts.push_back(tt);
        *tIter++;
      }
    }
    Term tt;
    if (op == Not || op == BVNot) {
      tt = solver_->make_term(op, ts[0]);
    } else if (op == Equal || op == And || op == Or || op == BVAnd || op == BVOr) {
      tt = solver_->make_term(op, {ts[0], ts[1]});
    } else if (op == Ite) {
      tt = solver_->make_term(op, {ts[0], ts[1], ts[2]});
    } else {
      throw std::runtime_error("??? - unrecognized op: " + op.to_string());
    }
    Term tseitinControlVar = makeControlVar("TSEITIN_" + std::to_string(tseitinIdx++));
    Sort boolSort = solver_->make_sort(SortKind::BOOL);
    string tseitinVarNamePrefix = "_tseitin_";
    string tseitinVarUntimedName = tseitinVarNamePrefix + std::to_string(tseitinIdx);
    Term tseitinVarUntimed = solver_->make_symbol(tseitinVarUntimedName, boolSort);
    tseitinVars.push_back(tseitinVarUntimed);
    tseitinVarToConstraint[tseitinVarUntimed] = tt;
    // Unroll the untimed Tseitin variable to `k` ticks
    TermVec tseitinVarAtAllTicksVec;
    for (int i = 0; i < k; i++) {
      Term tvAtTickI = solver_->make_symbol(tseitinVarUntimedName + "@" + std::to_string(i), boolSort);
      tseitinVarAtAllTicksVec.push_back(tvAtTickI);
    }
    Term tseitinVarAtAllTicks = makeConjunction(tseitinVarAtAllTicksVec);
    TermVec origTermDecomposedAndUnrolledVec;
    for (int i = 0; i < k; i++) {
      // Manually unroll Tseitin variable instances because pono's unroller
      // will only unroll variables present in the original model.
      Term untimedTerm = solver_->make_term(PrimOp::Equal, tseitinVarUntimed, tt);
      UnorderedTermMap termSubMapForI;
      for ( auto & tv: tseitinVars) {
        string tseitinVarAtTickIName = tv->to_string() + "@" + std::to_string(i);
        termSubMapForI[tv] = solver_->get_symbol(tseitinVarAtTickIName);
      }
      // Original term with original variables and Tseitin variables unrolled
      Term decomposedTermAtTickI = unroller_.at_time(solver_->substitute(untimedTerm, termSubMapForI), i);
      origTermDecomposedAndUnrolledVec.push_back(decomposedTermAtTickI);
    }
    Term origTermDecomposedAndUnrolled = makeConjunction(origTermDecomposedAndUnrolledVec);
    musAssertions[tseitinControlVar] = origTermDecomposedAndUnrolled;
    contextualAssert(solver_->make_term(Equal, tseitinVarUntimed, tseitinVarAtAllTicks));
    return tseitinVarUntimed;
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
    return makeControlVar(type, t->to_string());
  }

  Term Mus::makeControlVar(ConstraintType type, const string suffix)
  {
    return makeControlVar(constraintTypeToStr[type] + "_" + suffix);
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
   * Assert an atomic constraint that MUST can toggle during UNSAT core
   * minimization.
   */
  void Mus::musAssert(ConstraintType ct, Term cv, Term c, int k)
  {
    Term t_u;
    switch (ct) {
      case INIT:
        t_u = unroller_.at_time(c, 0);
        break;
      case INVAR:
      case TRANS:
        t_u = options_.mus_apply_tseitin_ ? tseitinDecompose(c, k) : unrollUntilBound(c, k);
        break;
      case SPEC:
        t_u = solver_->make_term(Not, unrollUntilBound(c, k));
        break;
    }
    musAssertions[cv] = t_u;
  }

  /*
   * Assert a constraint to the context in which MUST makes its satisfiability
   * determination. These constraints are not toggleable during UNSAT core
   * minimization.
   */
  void Mus::contextualAssert(Term constraint)
  {
    solver_->assert_formula(constraint);
    contextualAssertions.push_back(constraint);
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
     * <stateVar>.next = ...), then use that state variable's id for the
     * control var symbol. Otherwise use the conjunct's to_string as an
     * identifier.
     */
    unordered_map<string, Term> transIdToConjunct;
    for (auto &tc: transConjuncts) {
      Term id = tc;
      if (tc->get_op() == PrimOp::Equal) {
        Term lhs = *tc->begin();
        if (ts_.is_next_var(lhs)) {
          id = ts_.curr(lhs);
        }
      }
      if (!options_.mus_include_yosys_internal_netnames_ && isYosysInternalNetname(id)) {
        contextualAssert(unrollUntilBound(tc, k));
      } else {
        transIdToConjunct.insert({id->to_string(), tc});
      }
    }

    if (!options_.mus_combine_suffix_.empty()) {
      if (options_.mus_apply_tseitin_) {
        throw std::runtime_error("???");
      }
      /*
       * Conjoin TRANS constraints that are identical up to suffix matching the
       * supplied regular expression.
       */
      std::multimap<string, Term> mm;
      regex r(std::regex("(.*)" + options_.mus_combine_suffix_));
      for (auto & [id, tc] : unordered_map(transIdToConjunct)) {
        smatch m;
        if (regex_search(id, m, r)) {
          mm.insert({m[1], tc});
          transIdToConjunct.erase(id);
        }
      }
      for (auto & [id, tc] : mm) {
        if (transIdToConjunct.find(id) == transIdToConjunct.end()) {
          transIdToConjunct[id] = tc;
        } else {
          transIdToConjunct[id] = solver_->make_term(And, transIdToConjunct[id], tc);
        }
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
      musAssert(INIT, cv, ic, 0);
    }

    for (auto &tc: transIdToConjunct) {
      Term cv = makeControlVar(ConstraintType::TRANS, tc.first);
      musAssert(TRANS, cv, tc.second, k);
    }

    for(auto &c: ts_.constraints()) {
      Term cv = makeControlVar(ConstraintType::INVAR, c.first);
      musAssert(INVAR, cv, c.first, k);
    }

    Term spec = orig_property_.prop();
    logger.log(0, "Checking Spec: {}", spec);
    Term specCv = makeControlVar(ConstraintType::SPEC, spec);
    // Term negSpec = solver_->make_term(PrimOp::Not, spec);
    musAssert(SPEC, specCv, spec, k);

    for (auto &ma: musAssertions) {
      Term e = solver_->make_term(Equal, ma.first, ma.second);
      solver_->assert_formula(e);
    }

    if (options_.mus_dump_smt2_) {
      /*
       * LoggingSolver does not support dump_smt2, so we transfer all of our
       * assertions to a new BoolectorSolver
       */
      SmtSolver bs = BoolectorSolverFactory::create(false);
      bs->set_opt("rewrite-level", "0");
      TermTranslator tt = TermTranslator(bs);
      for(auto & e: musAssertions) {
        Term controlVar = e.first;
        Term musConstraint = e.second;
        bs->assert_formula(tt.transfer_term(controlVar));
        Term t = solver_->make_term(PrimOp::Equal, controlVar, musConstraint);
        bs->assert_formula(tt.transfer_term(t));
      }
      for(auto & ca: contextualAssertions) {
        bs->assert_formula(tt.transfer_term(ca));
      }
      bs->dump_smt2("mus_query.smt2");
    }

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
    std::sort(terms.begin(), terms.end(), [](const Term & a, const Term & b) {
      return a->to_string() < b->to_string();
    });
    return terms;
  }

  bool Mus::isYosysInternalNetname(Term t)
  {
    return t->is_symbol() && t->to_string().rfind('$', 0) == 0;
  }


}  // namespace pono
