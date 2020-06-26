#include <iostream>
#include <fstream>
#include <vector>

using namespace std;
//
int main(int argc, char** argv){

	string line, last_line;
	ifstream is;
	int nof = argc-1;
	string comb = "";

	if(nof){
		is.open(argv[nof]);
		while(getline(is, line)){
			comb += line + "\n";
			if(line == ":Constraints:")
				break;
		}
		is.close();
	}

	string cons = "";

	while(nof--){
		is.open(argv[nof+1]);
		last_line = "";
		//Can be made better.
		while(getline(is, line))
			if(line != "\n")
				last_line = line;

		//comb += last_line + "\n";
		if(cons == "")
			cons = last_line;
		else
			cons = "BOR(" + cons + ", " + last_line + ")";

		is.close();
	}

	comb = comb + cons;

	//cout<<comb<<"\n";

	ofstream out("/tmp/QCounter/comb.qcoral");

	out << comb;
    out.close();

	return 0;

}