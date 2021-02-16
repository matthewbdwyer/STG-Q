#include <iostream>
#include <fstream>
#include <vector>
#include <dirent.h>

using namespace std;
//
int main(int argc, char** argv){

	DIR *dir;
	struct dirent *entry;
	string dir_name = "/tmp/QCounter/out";
	dir = opendir(dir_name.c_str());
	int nof = 0, passed = 0;
	ifstream is;
	string expected;
	string ans;

	while( (entry = readdir(dir)) != NULL){

		if(entry->d_name[0] != '.'){
			nof++;
			string path = dir_name + "/" + string(entry->d_name);
			cout<<"Entry: "<<path<<endl;

			is.open(path);
			string line;

			while(getline(is, line)){
				if(line != "\n"){
					ans = expected;
					expected = line;
				}
			}

			is.close();


			int mean_pos = ans.find("mean=");
			int var_pos = ans.find("variance=");

			if(mean_pos == -1 || var_pos == -1){
				cout<<"Some error in the output file: "<< path <<"\n";
				break;
			}

			string mean, var;

			for(int i = mean_pos+5; ans[i] != ',' && i < ans.length(); i++)
				mean += ans[i];

			for(int i = var_pos+9; ans[i] != ',' && i < ans.length(); i++)
				var += ans[i];

			//cout<<mean<<" , "<< var<<"\n";

			int i = 0;
			string exp_mean, exp_var;

			for(i=0; i<expected.length() && expected[i] != ' '; i++)
				exp_mean += expected[i];

			i++;

			while(i<expected.length())
				exp_var += expected[i++];

			cout<<stod(exp_mean)<<" , "<<stod(exp_var)<<"\n";
			cout<<stod(mean)<<" , "<<stod(var)<<"\n";

			if(stod(mean)+stod(var) <= stod(exp_mean) + stod(exp_var) && stod(mean)-stod(var) >= stod(exp_mean) - stod(exp_var) )
				passed++;


		}
		
	}

	cout<<passed<<"/"<<nof<<" test cases passed\n";

	return 0;

}