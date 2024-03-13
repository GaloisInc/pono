
#include "mus.h"
#include "smt/available_solvers.h"
#include <regex>
#include "utils/logger.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    if (!options_.logging_smt_solver_) {
      throw invalid_argument("MUS engine requires the --logging-smt-solver flag");
    }
    engine_ = Engine::MUS_ENGINE;
    // TODO(rperoutka) - what does `full_model` do?
    boolector = create_solver_for(BTOR, BMC, false, true);
    toBoolectorInternal = new TermTranslator(boolector);
  }

  Mus::~Mus() {
    controlVars.clear();
    controlTerms.clear();
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

  Term Mus::unrollOrigTerm(Term t, int k)
  {
    return toBoolectorInternal->transfer_term(unroller_.at_time(t, k));
  }

  Term Mus::unrollUntilBound(Term t, int k)
  {
    TermVec uts;
    for (int i = 0; i < k; i++) {
      uts.push_back(unrollOrigTerm(t, i));
    }
    return makeConjunction(uts);
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
    string s = t->to_string();
    if (type == INVAR) {
      s = std::to_string(t->hash());
    }
    return makeControlVar(constraintTypeToStr[type] + "_" + s);
  }

  Term Mus::makeControlEquality(const Term& controlVar, const Term& constraint)
  {
    Term eqTerm = boolector->make_term(PrimOp::Equal, controlVar, constraint);
    controlTerms.push_back(eqTerm);
    return eqTerm;
  }

  Term Mus::makeConjunction(TermVec ts)
  {
    return ts.size() == 1 ? ts[0] : boolector->make_term(PrimOp::And, ts);
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
   * Construct a MUST Master object initialized with our MUS query by making
   * assertions to a BoolectorSolver object, dumping smt2 from the BoolectorSolver,
   * and passing the resulting smt2 off to MUST.
   *
   * The constraint set we set up for MUST to reason over consists of
   *  - `INIT` constraints (top-level conjuncts of TransitionSystem.init())
   *  - `TRANS` constraints (top-level conjuncts of TransitionSystem.trans())
   *  - `INVAR` constraints (elements of TransitionSystem.constraints())
   *  - `SPEC` the negation of the safety property
   *
   * For each element of the constraint set, we introduce a new symbol ("control
   * variable"). The CONTROL_TERMS constraint stipulates that for all control
   * variables, cv, cv holds iff its corresponding constraint holds.
   *
   * The approach of introducing new symbols and tying them to together with
   * CONTROL_TERMS is necessary to prevent BoolectorSolver from rewriting away
   * our intended constraint structure.
   *
   */
  Master Mus::buildMusQuery(int k)
  {


    UnorderedTermSet initConjuncts = extractTopLevelConjuncts(ts_.init());
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
      transIdToConjunct.insert({id, unrollUntilBound(tc, k)});
    }

    for (auto &ic: initConjuncts) {
      Term cv = makeControlVar(ConstraintType::INIT, ic);
      makeControlEquality(cv, unrollOrigTerm(ic, 0));
    }

    for (auto &tc: transIdToConjunct) {
      Term cv = makeControlVar(ConstraintType::TRANS, tc.first);
      makeControlEquality(cv, tc.second);
    }

    for(auto &c: ts_.constraints()) {
      Term cv = makeControlVar(ConstraintType::INVAR, c.first);
      makeControlEquality(cv, unrollUntilBound(c.first, k + 1));
    }

    Term spec = orig_property_.prop();
    logger.log(0, "Checking Spec: {}", spec);
    Term specCv = makeControlVar(ConstraintType::SPEC, spec);
    Term negSpec = boolector->make_term(PrimOp::Not, unrollUntilBound(spec, k + 1));
    makeControlEquality(specCv, negSpec);

    Term ctCv = makeControlVar(ConstraintType::CONTROL_TERMS);
    Term ce = makeControlEquality(ctCv, makeConjunction(controlTerms));
    boolector->assert_formula(ce);
    controlVars.push_back(ctCv);

    for(auto &cv: controlVars) {
      boolector->assert_formula(cv);
    }

    // TODO(rperoutka) - make query output location configurable
    string musQueryFile = ".musquery.smt2";
    boolector->dump_smt2(musQueryFile);

    boolectorAliasCleanup(musQueryFile);
    // MUST defaults to remus when alg isn't specified on CLI
    // TODO(rperoutka) - make alg configurable via CLI flag
    return Master(musQueryFile, "remus");
  }

  TermVec Mus::musAsOrigTerms(MUS mus)
  {
    // All MUSes should contain the CONTROL_TERMS infrastructure:
    assert(mus.bool_mus[0]);
    assert(mus.bool_mus[mus.bool_mus.size() - 1]);

    TermVec terms;
    /*
     * MUS elements at indices 0 and (mus.bool_mus.size() - 1) are the
     * CONTROL_TERMS infrastructure tying all other control vars to their
     * constaints. Don't include them in the returned MUS.
     */
    for(int i = 1; i < mus.bool_mus.size() - 1; i++) {
      if (mus.bool_mus[i]) {
          terms.push_back(controlVars.at(i-1));
      }
    }
    return terms;
  }

bool ends_with(std::string const & value, std::string const & ending)
  {
    if (ending.size() > value.size()) return false;
    return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
  }

  /*
   *  Boolector aliases `Bool` and `(_ BitVec 1)` internally. Its
   *  boolector_dump_smt2 method appears to attempt to explicit covert between
   *  the two in the resulting smt2, but there appears to be a bug when it's
   *  dealing with `select`s yeilding a `(_ BitVec 1)`.
   *
   *  This function explictly converts `select`s used as
   *    - conditions for `ite`s
   *    - the sole term in a fun returing `Bool`.
   */
  void Mus::boolectorAliasCleanup(string fname)
  {
    std::ifstream smtQuery(fname);
    std::stringstream buffer;
    buffer << smtQuery.rdbuf();
    std::vector<std::string> lines;
    std::istringstream stream2(buffer.str());

    while(!stream2.eof()) {
        std::string l;
        getline(stream2, l);
        lines.push_back(l);
    }

    for (int i = 1; i < lines.size(); i++) {
        std::string line = lines[i];
        size_t idx = line.rfind("(select");
        if (idx != std::string::npos) {
            if (ends_with(lines[i - 1], "(ite ") || lines[i - 1].rfind("() Bool") != std::string::npos) {
                int lineNo = i;
                int selectEndLineNo = -1;
                int selectEnd = -1;
                int parensToClose = 0;
                while (lineNo < lines.size() && selectEndLineNo == -1) {
                    std::string _line = lines[lineNo];
                    for(int j = 0; j < _line.size(); j++) {
                        char c = _line[j];
                        if (c == '(') {
                            parensToClose++;
                        } else if (c == ')') {
                            parensToClose--;
                            if (parensToClose == 0) {
                                selectEnd = j;
                                selectEndLineNo = lineNo;
                                break;
                            }
                        }
                    }
                    lineNo++;
                }
                lines[selectEndLineNo].insert(selectEnd + 1, " #b1) true false)");
                lines[i].insert(idx, "(ite (= ");
            }
        }
    }
    std::ofstream out(fname);
    vector<string> aliasFuns = {
      "(define-fun not ((a (_ BitVec 1))) Bool (ite (= a #b1) true false))",
      "(define-fun and ((a (_ BitVec 1)) (b Bool)) Bool (ite (= a #b1) b false))"};
    for(auto &l: aliasFuns) out << l << std::endl;
    bool skip = true;
    for(auto &l: lines) {
      if (skip) {
        // BoolectorSolver.dump_smt2 adds a `(set-logic QF_UFBV)` on the first
        // line. Boolector seems to accept the use of arrays within this, but
        // Z3 does not. Just delete the line erronous `set-logic` for now.
        // TODO(rperoutka) - perhaps swap it to `(set-logic QF_AUFBV)`? Is there a performance benefit to this?
        skip = false;
      } else {
        out << l << std::endl;
      }
    }
  }
}  // namespace pono
