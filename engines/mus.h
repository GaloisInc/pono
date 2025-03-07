#pragma once

#include <Master.h>

#include "engines/prover.h"

namespace pono {

class Mus : public Prover
{
public:
  Mus(const Property & p, const TransitionSystem & ts,
      const smt::SmtSolver & solver,
      PonoOptions opt = PonoOptions());

  ~Mus();

  typedef Prover super;

  ProverResult check_until(int k) override;
  std::vector<MUS> check_until_yielding_muses(int k);
  Master buildMusQuery(int k);

private:
  enum ConstraintType {
    INIT,
    TRANS,
    INVAR,
    SPEC,
    CONTROL_TERMS
  };
  unordered_map<ConstraintType, string> constraintTypeToStr{
    {INIT, "INIT"},
    {TRANS, "TRANS"},
    {INVAR, "INVAR"},
    {SPEC, "SPEC"}
  };
  smt::TermVec controlVars;
  smt::UnorderedTermMap musAssertions;
  smt::TermVec contextualAssertions;

  smt::TermVec tseitinVars;
  smt::UnorderedTermMap tseitinVarToConstraint;
  smt::UnorderedTermSet extractTopLevelConjuncts(smt::Term conjunction);
  void musAssert(ConstraintType ct, smt::Term cv, smt::Term constraint, int kcd);
  void contextualAssert(smt::Term constraint);
  smt::Term unrollUntilBound(smt::Term t, int k);
  smt::Term makeConjunction(smt::TermVec ts);
  smt::Term makeControlVar(string id);
  smt::Term makeControlVar(ConstraintType type);
  smt::Term makeControlVar(ConstraintType type, smt::Term t);
  smt::Term makeControlVar(ConstraintType type, string s);
  std::vector<smt::Term> musAsOrigTerms(MUS mus);
  void boolectorAliasCleanup(string fname);
  static bool isYosysInternalNetname(smt::Term t);
  int tseitinIdx = 0;
  smt::Term tseitinDecompose(smt::Term t, int k);
};  // class Mus

}  // namespace pono
