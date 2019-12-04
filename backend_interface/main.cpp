#include <libsnark/relations/variable.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
#include <libff/common/default_types/ec_pp.hpp>
using namespace libsnark;
typedef libff::bn128_pp pp;
typedef libff::Fr<pp> Fr;
/*
r1cs_constraint_system<pp> to_cs() {


}
*/
int main(int argc, char** argv) {
  /*
  if (argc < 3) {
    std::cerr << argv[0] << " constraint_file input_file" << std::endl;
    }*/
  libff::bn128_pp::init_public_params();
  variable<Fr> v(1);
  auto lt = linear_term<Fr>(v);
  auto lc = linear_combination<Fr>(lt);
  auto single_cs = r1cs_constraint<Fr>(lc, lc, lc);
  auto cs = r1cs_constraint_system<Fr>();
  cs.primary_input_size = 0;
  cs.auxiliary_input_size = 1;
  cs.constraints = { single_cs };
  auto keypair = r1cs_ppzksnark_generator<pp>(cs);
}
