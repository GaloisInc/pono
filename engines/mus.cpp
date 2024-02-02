
#include "mus.h"
#include <fstream>

#include "Master.h"

using namespace smt;

namespace pono {

  Mus::Mus(const Property & p, const TransitionSystem & ts, const SmtSolver & solver, PonoOptions opt): super(p, ts, solver, opt) {
    engine_ = Engine::MUS_ENGINE;
  }

  Mus::~Mus() {}

  ProverResult Mus::check_until(int k) {
    Master solver("???", "???");
    return ProverResult::TRUE;
  }

}  // namespace pono
