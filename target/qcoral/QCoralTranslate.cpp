#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "QCoralPrinter.h"

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
    QCoralPrinter qcp(std::cout, 2);
    qcp.print(constraint.value());
  } else {
    cout << "STG parse error\n";
  }
}
