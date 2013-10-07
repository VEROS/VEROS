#include <iostream>
#include <fstream>
#include <vector>
#include "getopt_pp.hxx"

using namespace GetOpt;
using namespace std;

#define LINE 256

int main(int argc, char* argv[]){
  GetOpt_pp args(argc, argv);
  string input;
  string output;
  bool ask = false;

  args >> Option('i', "input", input);
  args >> Option('o', "output", output);
  args >> Option('a', "ask", ask);

  string content, result;
  try{
    ifstream inf(input.c_str());
    if(inf.is_open()){
      cout << "reading input file" << endl;

      vector<string> lines;
      string recordName;
      string constructor;
      bool record = false;
      string prefix;
      size_t comment_start, comment_end;
      bool commenting = false;
      result += string("Set Implicit Arguments.\n\n") +
        "Require Import " + input.substr(0, input.find(".v")) + ".\n\n";
      while(getline(inf, content)){
        //cout << content << endl;

        if(!commenting){
          if((comment_start = content.find("(*")) != string::npos){
            if((comment_end = content.find("*)")) != string::npos){
              content.erase(comment_start, comment_end + 2 - comment_start);
            }
            else{
              content.erase(comment_start, string::npos);
              commenting = true;
            }
          }
        }
        else{
          if((comment_end = content.find("*)")) != string::npos){
            content.erase(0, comment_end + 2);
            commenting = false;
          }
          else{
            continue;
          }
        }

        if(content.find_first_not_of(" \t") == string::npos)
          continue;

        if(!record){
          size_t name_start = 0;
          if((name_start = content.find("Record")) != string::npos){
            cout << content << endl;
            name_start += 6;
            name_start = content.find_first_not_of(" ", name_start);
            size_t name_end = content.find_first_of(" :", name_start);

            cout << name_end << " " <<
              content.find_first_of(" :", name_start, 100) << endl;

            recordName = content.substr(name_start, name_end - name_start);

            size_t cstr_start = content.find_first_not_of(" :=", name_end);
            size_t cstr_end = content.find_first_of("{ \n", cstr_start);

            cout << cstr_end << " " <<
              content.find_first_of("{ \n", cstr_start, 100) << endl;

            constructor = content.substr(cstr_start, cstr_end - cstr_start);
            record = true;
            lines.clear();
          }
        }
        else{
          if(content.find_first_of("}") == string::npos){
            int field_start = content.find_first_not_of(" \t");
            int field_end = content.find_first_of(" :", field_start);
            lines.push_back(content.substr(field_start, field_end - field_start));
          }
          else{
            prefix.clear();
            record = false;
            if(ask){
              cout << "Record: " << recordName << endl;
              cout << "Would you like to add a prefix for getting and setting functions?"
                   << endl;
              cout << "Input a prefix or hit return to skip this one"
                   << endl;
              cin >> prefix;
            }
            unsigned int now = 0;
            result += string("(***************** Record ") + recordName +
              " *****************)\n";
            for(vector<string>::iterator it = lines.begin();
                it != lines.end(); it++){
              result += string("Definition") + prefix + " get_" + *it
                + " a := a.(" + *it + ").\n\n";
              result += string("Definition") + prefix + " set_" + *it
                + " a v :=\n\t" + "match a with\n\t" + constructor;
              for(unsigned int index = 0; index < lines.size(); index++){
                char buff[10];
                sprintf(buff, "%d", index);
                result += string(" a") + buff;
              }
              result += string("\n\t") + "=> " + constructor;
              for(unsigned int index = 0; index < lines.size(); index++){
                if(index != now){
                  char buff[10];
                  sprintf(buff, "%d", index);
                  result += string(" a") + buff;
                }
                else{
                  result += string(" v");
                }
              }
              result += string("\n\t") + "end.\n\n";
              now++;
            }
            result += string("(******************* End ") + recordName +
              " *******************)\n\n";
          }
        }
      }

      ofstream outf(output.c_str());
      if(outf.is_open()){
        outf << result;
      }
    }
  }
  catch(const exception& e){
    cerr << e.what() << endl;
  }
  return 0;
}
