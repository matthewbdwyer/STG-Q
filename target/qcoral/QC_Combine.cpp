#include <iostream>
#include <fstream>
#include <vector>
#include <string>

using namespace std;

/*! \fn main
* \brief Generate a single comb.qcoral file from multiple qcoral files.
*
* Apply a disjuction (OR) in multiple path conditions.
* \param argc the number of files passed.
* \param argv pointer array which points to the location of all the individual qcoral files. 
* \return the combined file (comb.qcoral) in which the quantification is performed.
 */
int main(int argc, char** argv){

	string line, last_line;
	ifstream is;
	int nof = argc-1;
	string comb = "";
	string append = "";

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
		int loc = last_line.find(';');
		string before = last_line;
		string after = "";

		if( loc != -1){
			before = last_line.substr(0, loc);
			after =  last_line.substr(loc, last_line.length());
		}

		if(cons == "")
			cons = before;
		else
			cons = "BOR(" + cons + ", " + before + ")";

		if(append == "")
			append = after;
		else
			append += after;

		is.close();
	}

	comb = comb + cons + append;

	ofstream out("/tmp/QCounter/comb.qcoral");

	out << comb;
    out.close();
	return 0;

}
