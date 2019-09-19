#include <iostream>

#include "optionparser.h"
#include "smt-switch/boolector_factory.h"

#include "bmc.h"
#include "defaults.h"
#include "frontends/btor2_encoder.h"
#include "kinduction.h"
#include "prop.h"

using namespace cosa;
using namespace smt;
using namespace std;

/************************************* Option Handling setup *****************************************/
// from optionparser-1.7 examples -- example_arg.cc
enum optionIndex { UNKNOWN_OPTION, HELP, INDUCTION, BOUND, PROP };

struct Arg : public option::Arg
{
  static void printError(const char* msg1, const option::Option& opt, const char* msg2)
  {
    fprintf(stderr, "%s", msg1);
    fwrite(opt.name, opt.namelen, 1, stderr);
    fprintf(stderr, "%s", msg2);
  }

  static option::ArgStatus Numeric(const option::Option& option, bool msg)
  {
    char* endptr = 0;
    if (option.arg != 0 && strtol(option.arg, &endptr, 10)){};
    if (endptr != option.arg && *endptr == 0)
      return option::ARG_OK;

    if (msg) printError("Option '", option, "' requires a numeric argument\n");
    return option::ARG_ILLEGAL;
  }
};

const option::Descriptor usage[] =
  {
   {UNKNOWN_OPTION, 0, "", "", Arg::None, "USAGE: cosa2 [options] <btor file>\n\n"
    "Options:"},
   {HELP, 0, "", "help", Arg::None, "  --help \tPrint usage and exit."},
   {INDUCTION, 0, "i", "induction", Arg::None, "  --induction, -i \tUse temporal k-induction."},
   {BOUND, 0, "k", "bound", Arg::Numeric, "  --bound, -k \tBound to check up until."},
   {PROP, 0, "p", "prop", Arg::Numeric, "  --prop, -p \tProperty index to check (default: 0)."},
   {0,0,0,0,0,0}
  };
/*********************************** end Option Handling setup ***************************************/

int main(int argc, char ** argv)
{
  argc-=(argc>0); argv+=(argc>0); // skip program name argv[0] if present
  option::Stats  stats(usage, argc, argv);
  std::vector<option::Option> options(stats.options_max);
  std::vector<option::Option> buffer(stats.buffer_max);
  option::Parser parse(usage, argc, argv, &options[0], &buffer[0]);

  if (parse.error())
  {
    return 1;
  }

  if (options[HELP] || argc == 0)
  {
    option::printUsage(cout, usage);
    return 0;
  }

  if (parse.nonOptionsCount() != 1)
  {
    option::printUsage(cout, usage);
    return 1;
  }

  bool unknown_options = false;
  for (option::Option* opt = options[UNKNOWN_OPTION]; opt; opt = opt->next())
  {
    unknown_options = true;
  }

  if (unknown_options)
  {
    option::printUsage(cout, usage);
    return 1;
  }

  bool induction=default_induction;
  unsigned int prop_idx=default_prop_idx;
  unsigned int bound=default_bound;

  for (int i = 0; i < parse.optionsCount(); ++i)
  {
    option::Option& opt = buffer[i];
    switch (opt.index())
    {
    case HELP:
      // not possible, because handled further above and exits the program
    case INDUCTION:
      induction=true;
      break;
    case BOUND:
      bound=atoi(opt.arg);
      break;
    case PROP:
      prop_idx=atoi(opt.arg);
      break;
    case UNKNOWN_OPTION:
      // not possible because Arg::Unknown returns ARG_ILLEGAL
      // which aborts the parse with an error
      break;
    }
  }

  string filename(parse.nonOption(0));

  SmtSolver s = BoolectorSolverFactory::create();
  s->set_opt("produce-models", true);
  s->set_opt("incremental", true);

  RelationalTransitionSystem rts(s);
  BTOR2Encoder btor_enc(filename, rts);

  cout << "Created TransitionSystem with:\n";
  cout << "\t" << rts.inputs().size() << " input variables." << endl;
  cout << "\t" << rts.states().size() << " state variables." << endl;

  cout << "Inputs:" << endl;
  for (auto i : rts.inputs())
  {
    cout << "\t" << i << endl;
  }

  cout << "States:" << endl;
  for (auto s : rts.states())
  {
    cout << "\t" << s << endl;
  }

  unsigned int num_bad = btor_enc.badvec().size();
  if (prop_idx >= num_bad)
  {
    cout << "Property index " << prop_idx;
    cout << " is greater than the number of bad tags in the btor file (";
    cout << num_bad << ")" << endl;
    return 1;
  }

  Term bad = btor_enc.badvec()[prop_idx];
  Property p(rts, s->make_term(PrimOp::Not, bad));

  std::shared_ptr<Prover> prover;
  if (induction)
  {
    cout << "Running k-induction" << endl;
    prover = std::make_shared<KInduction>(p, s);
  }
  else
  {
    cout << "Running bounded model checking" << endl;
    prover = std::make_shared<Bmc>(p, s);
  }

  ProverResult r = prover->check_until(bound);
  if (r == FALSE) {
    cout << "Property " << prop_idx << " is FALSE" << endl;
    std::vector<UnorderedTermMap> cex;
    if (prover->witness(cex)) {
      for (size_t j = 0; j < cex.size(); ++j) {
        cout << "-------- " << j << " --------" << endl;
        const UnorderedTermMap &map = cex[j];
        for (auto v : map) {
          cout << v.first << " := " << v.second << endl;
        }
      }
    }
  } else if (r == TRUE) {
    cout << "Property " << prop_idx << " is TRUE" << endl;
  } else {
    cout << "Property " << prop_idx << " is UNKNOWN" << endl;
  }

  return 0;
}