#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "SMTPrinter.h"

using namespace std;

int main(int argc, const char *argv[]) {
  std::ifstream filestream;
  std::istream& stream = (argc == 1) ? cin : filestream;
  if (argc > 1) {
    filestream.open(argv[1]);
  }

  auto constraint = Constraint::parse(stream);

  if (constraint) {

    // cout << "STG parsesd successfully\n";
    SMTPrinter smtp(std::cout, 2);
    smtp.print(constraint.value());
  } else {
    cout << "STG parse error\n";
  }
}
