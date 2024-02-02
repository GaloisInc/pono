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

};  // class Mus

}  // namespace pono
