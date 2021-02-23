#include <ENCRYPTO_utils/crypto/crypto.h>
#include <ENCRYPTO_utils/parse_options.h>
#include <abycore/aby/abyparty.h>
#include <abycore/circuit/share.h>
#include <abycore/circuit/booleancircuits.h>
#include <abycore/sharing/sharing.h>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <math.h>
#include <string>
#include <abycore/circuit/arithmeticcircuits.h>

void read_test_options(int32_t *argcp, char ***argvp, e_role *role,
					   uint32_t *bitlen, uint32_t *nvals, uint32_t *secparam, std::string *address,
					   uint16_t *port, int32_t *test_op, uint32_t *test_bit, int *choose)
{

	uint32_t int_role = 0, int_port = 0, int_testbit = 0, int_choose = 0;

	parsing_ctx options[] =
		{{(void *)&int_role, T_NUM, "r", "Role: 0/1", true, false},
		 {(void *)&int_testbit, T_NUM, "i", "test bit", false, false},
		 {(void *)nvals, T_NUM, "n", "Number of parallel operation elements", false, false},
		 {(void *)bitlen, T_NUM, "b", "Bit-length, default 32", false, false},
		 {(void *)secparam, T_NUM, "s", "Symmetric Security Bits, default: 128", false, false},
		 {(void *)address, T_STR, "a", "IP-address, default: localhost", false, false},
		 {(void *)&int_port, T_NUM, "p", "Port, default: 7766", false, false},
		 {(void *)test_op, T_NUM, "t", "Single test (leave out for all operations), default: off", false, false},
		 {(void *)&int_choose, T_NUM, "c", "choose:(0) + (1) - (2) × (3) A2B (4) B2A ", false, false}};

	if (!parse_options(argcp, argvp, options,
					   sizeof(options) / sizeof(parsing_ctx)))
	{
		print_usage(*argvp[0], options, sizeof(options) / sizeof(parsing_ctx));
		std::cout << "Exiting" << std::endl;
		exit(0);
	}

	assert(int_role < 2);
	*role = (e_role)int_role;

	if (int_port != 0)
	{
		assert(int_port < 1 << (sizeof(uint16_t) * 8));
		*port = (uint16_t)int_port;
	}
	*choose = int_choose;
	*test_bit = int_testbit;
}

void test(e_role role, const std::string &address, uint16_t port, seclvl seclvl, uint32_t nvals, uint32_t nthreads,
		  e_mt_gen_alg mt_alg, e_sharing sharing,int choose)
{
	// for addition we operate on doubles, so set bitlen to 64 bits
	uint32_t bitlen = 32;
	ABYParty *party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg, 100000);
	std::vector<Sharing *> &sharings = party->GetSharings();
	//Circuit *circ = (Circuit *)sharings[sharing]->GetCircuitBuildRoutine();
    BooleanCircuit *bool_circ = (BooleanCircuit *)sharings[S_BOOL]->GetCircuitBuildRoutine();

    float f_opta = 48.0F,f_optb = 12.0F,fans = 0.0F;
	uint32_t *faPtr = (uint32_t *)&f_opta;
	uint32_t *fbPtr = (uint32_t *)&f_optb;
	share *s_fopta = bool_circ->PutINGate(faPtr,bitlen,SERVER);
	share *s_foptb = bool_circ->PutINGate(fbPtr,bitlen,SERVER);
	share *s_ans, *s_out;
	//share *s_fans,*s_fout;
    // s_ans = circ->PutFPGate(s_fopta,s_foptb,DIV);//PutFPGate
	s_ans=bool_circ->PutFPGate(s_fopta,s_foptb,DIV);
	   // s_ans = circ->PutMULGate(s_opta,s_optb);
    fans = f_opta / f_optb;
    std::cout << "| BS_SecDIV |" << std::endl;

    s_out = bool_circ->PutOUTGate(s_ans, ALL);

	// run
	party->ExecCircuit();
	

    uint32_t *s_out_out = (uint32_t *)s_out->get_clear_value_ptr();
	float s_out_out_f = *((float *)s_out_out);

	std::cout << "-------------------------------" << std::endl;
	std::cout << "| " << f_opta << "/"<< f_optb << " | ans: " << s_out_out_f << " | check: " << fans<< " |" << std::endl;
	std::cout << "-------------------------------\n"
				  << std::endl;
	

}
 

int main(int argc, char **argv)
{
	e_role role;
	uint32_t bitlen = 1, nvals = 4, secparam = 128, nthreads = 1;

	uint16_t port = 7766;
	std::string address = "127.0.0.1";
	int32_t test_op = -1;
	e_mt_gen_alg mt_alg = MT_OT;
	uint32_t test_bit = 0;
	int choose = 0;

	read_test_options(&argc, &argv, &role, &bitlen, &nvals, &secparam, &address,
					  &port, &test_op, &test_bit, &choose);
    // read_test_options(&argc, &argv, &role, &bitlen, &nvals, &secparam, &address,
	// 				  &port, &test_op, &test_bit);

	seclvl seclvl = get_sec_lvl(secparam);
	e_sharing sharing = choose > 3 ? S_BOOL : S_ARITH;
	//test(role, address, port, seclvl, nvals, nthreads, mt_alg, sharing, choose);
    test(role, address, port, seclvl, nvals, nthreads, mt_alg, S_BOOL,choose);
	return 0;
}
