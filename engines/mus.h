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
    {SPEC, "SPEC"},
    {CONTROL_TERMS, "CONTROL_TERMS"}
  };
  smt::TermTranslator* toBoolectorInternal;
  smt::TermVec controlVars;
  smt::TermVec controlTerms;
  smt::SmtSolver boolector;
  void assert_formula(smt::Term t, smt::TermTranslator tt);
  smt::UnorderedTermSet extractTopLevelConjuncts(smt::Term conjunction);
  Master buildMusQuery(int k);
  smt::Term unrollOrigTerm(smt::Term t, int i);
  smt::Term makeConjunction(smt::TermVec ts);
  smt::Term makeControlVar(string id);
  smt::Term makeControlVar(ConstraintType type);
  smt::Term makeControlVar(ConstraintType type, smt::Term t);
  smt::Term makeControlEquality(const smt::Term& controlVar, const smt::Term& constraint);
  std::vector<smt::Term> musAsOrigTerms(MUS mus);
  void boolectorAliasCleanup(string fname);
};  // class Mus

}  // namespace pono
