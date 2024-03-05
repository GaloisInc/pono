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
  Master buildMusQuery(int k);
  void assertInitConstraints();
  void assertUnrolledTransConstraints(int k);
  void assertUnrolledSpec(int k);
};  // class Mus

}  // namespace pono