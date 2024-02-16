#pragma once

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

private:
  void assertInitConstraints();
  void assertUnrolledTransConstraints(int k);
  void assertUnrolledSpec(int k);
};  // class Mus

}  // namespace pono
