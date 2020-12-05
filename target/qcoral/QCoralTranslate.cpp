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

  else{
    cout<<"No File location given\n";
    return -1;
  }

  auto constraint = Constraint::parse(stream);

  if (constraint) {

    QCoralPrinter qcp(std::cout, 2);
    if(argc > 2)
      qcp.print(constraint.value(), argv[2]);
    else{
      std::cerr<<"No dictionary file given! Setting default params.\n";
      qcp.print(constraint.value(), NULL);
    }
  } else {
    cout << "STG parse error\n";
  }
}
