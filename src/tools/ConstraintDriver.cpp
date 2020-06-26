#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <optional>

#include "Constraint.h"
#include "ConstraintPrinter.h"

using namespace std;

int main(int argc, const char *argv[]) {
  if (argc > 2) {
    cout << "Expected fewer arguments.  Constraint read from stdin, with 0 arguments, or from a file given as the sole argument.\n";
    return -1;
  }

  std::ifstream filestream;
  std::istream& stream = (argc == 1) ? cin : filestream;
  if (argc > 1) {
    filestream.open(argv[1]);
  }

  if (auto constraint = Constraint::parse(stream); constraint) {
    ConstraintPrinter cp(std::cout, 2);
    cp.print(constraint.value());
  } else {
    cout << "STG parse error\n";
  }
}
