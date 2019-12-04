#include <libsnark/relations/variable.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
#include <libff/common/default_types/ec_pp.hpp>

#include <iostream>
#include <sstream>
#include <fstream>
using std::ifstream;
using std::istringstream;
using std::string;
using std::cout;
using std::endl;
using std::ios;

using namespace libsnark;
typedef libff::bn128_pp pp;
typedef libff::Fr<pp> Fr;

r1cs_constraint_system<Fr> to_cs(ifstream& constraintFile) {
  string buf;
  std::getline(constraintFile, buf);
  unsigned long primary_input_size = std::stoi(buf);
  std::getline(constraintFile, buf);

  unsigned long all_input_size = std::stoi(buf);
  unsigned long auxiliary_input_size = all_input_size - primary_input_size;
  cout << "primary_input_size: " << primary_input_size << endl;
  cout << "auxiliary_input_size: " << auxiliary_input_size << endl;
  auto cs = r1cs_constraint_system<Fr>();
  cs.primary_input_size = primary_input_size;
  cs.auxiliary_input_size = auxiliary_input_size;
  std::vector<r1cs_constraint<Fr>> constraints;
  while (getline(constraintFile, buf)) {
    auto lc = linear_combination<Fr>();
    istringstream ss(buf);
    string directive;
    ss >> directive;
    if (directive == "IAdd") {
      string constant;
      ss >> constant;
      auto constLit = Fr(constant.c_str());
      lc = lc + constLit;
      string buf1; // coeff
      while (ss >> buf1) {
        string buf2; // var
        ss >> buf2;
        auto coeff = Fr(buf1.c_str());
        auto var = variable<Fr>(std::stoi(buf2));
        lc = lc + (coeff * var);
      }
      constraints.push_back(r1cs_constraint<Fr>(lc, 1, 0));
    }
    else if (directive == "IMul") {
      string a;
      string b;
      string c;
      string d;
      string e;
      ss >> a >> b >> c >> d >> e;
      auto coeffA = Fr(a.c_str());
      auto varB = variable<Fr>(std::stoi(b));
      auto varC = variable<Fr>(std::stoi(c));
      auto coeffD = Fr(d.c_str());
      auto varE = variable<Fr>(std::stoi(e));
      constraints.push_back(r1cs_constraint<Fr>(coeffA * varB, varC, coeffD * varE));
    }
  }
  cs.constraints = constraints;
  return cs;
}

std::vector<Fr> read_input(ifstream& inputFile, size_t size) {
  auto result = std::vector<Fr> {};
  string linebuf;
  for (size_t i = 0; i < size; ++i) {
    getline(inputFile, linebuf);
    istringstream ss(linebuf);
    string var_idx;
    string var_val;
    ss >> var_idx >> var_val;
    result.push_back(Fr(var_val.c_str()));
  }
  return result;
}


int main(int argc, char** argv) {
  
  if (argc < 3) {
    std::cerr << "Usage: " << argv[0] << " constraint_file input_file" << std::endl;
    exit(1);
  }
  string buf;
  ifstream constraintFile;
  constraintFile.open(argv[1], ios::in);
  ifstream inputFile;
  inputFile.open(argv[2], ios::in);
  libff::bn128_pp::init_public_params();

  auto cs = to_cs(constraintFile);
  cout << "constraints: " << cs.num_constraints() << endl;
  auto keypair = r1cs_ppzksnark_generator<pp>(cs);
  getline(inputFile, buf); // discards the first line
  auto primary_input = read_input(inputFile, cs.primary_input_size);
  auto auxiliary_input = read_input(inputFile, cs.auxiliary_input_size);
  auto prf = r1cs_ppzksnark_prover(keypair.pk, primary_input, auxiliary_input);
  auto verifier_result = r1cs_ppzksnark_verifier_strong_IC(keypair.vk, primary_input, prf);
  if (verifier_result) {
    cout << "proof is accepted by verifier" << endl;
  }
  else {
    cout << "proof is not accepted by verifier" << endl;
  }
}
