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
		  e_mt_gen_alg mt_alg, e_sharing sharing, int choose)
{
	// for addition we operate on doubles, so set bitlen to 64 bits
	uint32_t bitlen = 32;
	ABYParty *party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg, 100000);
	std::vector<Sharing *> &sharings = party->GetSharings();
	Circuit *circ = (Circuit *)sharings[sharing]->GetCircuitBuildRoutine();

	uint32_t opta = 48, optb = 12, ans;
	share *s_opta = circ->PutINGate(opta, bitlen, SERVER);
	share *s_optb = circ->PutINGate(optb, bitlen, SERVER);
	share *s_ans, *s_out;
	switch (choose)
	{
	case 0:
		s_ans = circ->PutADDGate(s_opta, s_optb);
		ans = opta + optb;
		break;
	case 1:
		s_ans = circ->PutSUBGate(s_opta, s_optb);
		ans = opta - optb;
		break;
	case 2:
		s_ans = circ->PutMULGate(s_opta, s_optb);
		ans = opta * optb;
		break;
	case 3:
	{
		Circuit *yc = sharings[S_YAO]->GetCircuitBuildRoutine();
		Circuit *bc = sharings[S_BOOL]->GetCircuitBuildRoutine();
		bc->PutA2BGate(s_opta, yc);
		std::cout << "| A2B |" << std::endl;
	}
	break;
	case 4:
	{
		Circuit *ac = sharings[S_ARITH]->GetCircuitBuildRoutine();
		ac->PutB2AGate(s_opta);
		std::cout << "| B2A |" << std::endl;
	}
	break;
	case 5:
	{
		s_ans = circ->PutGTGate(s_opta, s_optb);
		ans = (opta > optb) ? 1 : 0;
	}
	break;
    case 6:
    {
        s_ans = circ->PutADDGate(s_opta,s_optb);
        ans = opta + optb;
        std::cout << "| BS_SecADD |" << std::endl;
    }
    break;
    case 7:
    {
        s_ans = circ->PutSUBGate(s_opta,s_optb);
        ans = opta - optb;
        std::cout << "| BS_SecSUB |" << std::endl;
    }
    break;
    case 8:
    {
        s_ans = circ->PutMULGate(s_opta,s_optb);
        ans = opta * optb;
        std::cout << "| BS_SecMUL |" << std::endl;
    }
    break;
	default:
		exit(1);
		break;
	}
	if (choose < 3 || choose > 4)
		s_out = circ->PutOUTGate(s_ans, ALL);

	// run
	party->ExecCircuit();
	if (choose < 3 || choose > 4)
	{
		uint32_t out_val = s_out->get_clear_value<uint32_t>();
		std::cout << "-------------------------------" << std::endl;
		if (choose == 5)
			choose -= 2;
        if(choose == 6 || choose == 7 || choose == 8){
            choose -= 6;
        }
		std::string flags[4] = {"+", "-", "×", ">"};
		std::cout << "| " << opta << flags[choose] << optb << " | ans: " << out_val << " | check: " << ans<< " |" << std::endl;
		std::cout << "-------------------------------\n"
				  << std::endl;
	}
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

	seclvl seclvl = get_sec_lvl(secparam);
	e_sharing sharing = choose > 3 ? S_BOOL : S_ARITH;
	test(role, address, port, seclvl, nvals, nthreads, mt_alg, sharing, choose);
	return 0;
}
