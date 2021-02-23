#include <ENCRYPTO_utils/crypto/crypto.h>
#include <ENCRYPTO_utils/parse_options.h>
#include <ENCRYPTO_utils/thread.h>
#include <abycore/sharing/sharing.h>
#include <abycore/aby/abyparty.h>
#include <abycore/circuit/booleancircuits.h>
#include <abycore/circuit/arithmeticcircuits.h>
#include <iostream>
#include <cstdlib>
#include <ctime>

int32_t read_test_options(int32_t *argcp, char ***argvp, e_role *role,
						  uint32_t *bitlen, uint32_t *numbers, uint32_t *secparam, std::string *address,
						  uint16_t *port, int32_t *test_op)
{

	uint32_t int_role = 0, int_port = 0;

	parsing_ctx options[] =
		{{(void *)&int_role, T_NUM, "r", "Role: 0/1", true, false},
		 {(void *)numbers, T_NUM, "n", "Number of elements for inner product, default: 128", false, false},
		 {(void *)bitlen, T_NUM, "b", "Bit-length, default 16", false, false},
		 {(void *)secparam, T_NUM, "s", "Symmetric Security Bits, default: 128", false, false},
		 {(void *)address, T_STR, "a", "IP-address, default: localhost", false, false},
		 {(void *)&int_port, T_NUM, "p", "Port, default: 7766", false, false},
		 {(void *)test_op, T_NUM, "t", "Single test (leave out for all operations), default: off",
		  false, false}};

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

	return 1;
}

share *DecimalPlace(uint32_t bitlen, share *s_exponent, BooleanCircuit *circ)
{

	uint32_t zero = 0;
	share *s_temp = circ->PutCONSGate(zero, bitlen);
	share *s_move = circ->PutCONSGate(zero, bitlen);

	for (int i = 0; i < bitlen; i++)
	{
		s_temp->set_wire_id(i, s_exponent->get_wire_id(bitlen - (i + 1)));
	}

	for (int i = 0; i < 8; i++)
	{
		s_move->set_wire_id(i, s_temp->get_wire_id(8 - i));
	}

	return s_move;
}

share *div(share *opta, share *optb, uint32_t bitlen, BooleanCircuit *bool_circ)
{

	uint32_t optaWires[8], optbWires[8];
	float A = 2.8235294; // 48/17
	float B = 1.8823529; // 32/17
	uint32_t *aptr = (uint32_t *)&A;
	uint32_t *bptr = (uint32_t *)&B;
	share *s_a = bool_circ->PutCONSGate(aptr, bitlen);
	share *s_b = bool_circ->PutCONSGate(bptr, bitlen);
	uint32_t a = 126;
	share *temp = bool_circ->PutCONSGate(a, bitlen);

	share *s_nDecimalPlace = DecimalPlace(bitlen, optb, bool_circ);
	share *s_mDecimalPlace = DecimalPlace(bitlen, opta, bool_circ);

	for (uint32_t i = 0; i < 8; i++)
	{
		optbWires[i] = optb->get_wire_id(23 + i);
		optb->set_wire_id(23 + i, temp->get_wire_id(i));
	}
	share *s_nChangeDecimalPlace = DecimalPlace(bitlen, optb, bool_circ);

	share *s_nDvalue = bool_circ->PutSUBGate(s_nDecimalPlace, s_nChangeDecimalPlace);

	share *s_mChangeDecimalPlace = bool_circ->PutSUBGate(s_mDecimalPlace, s_nDvalue);

	for (uint32_t i = 0; i < 8; i++)
	{
		optaWires[i] = opta->get_wire_id(23 + i);
		opta->set_wire_id(23 + i, s_mChangeDecimalPlace->get_wire_id(i));
	}
	share *x_0 = bool_circ->PutFPGate(s_b, optb, MUL, bitlen, 1); //s_n为除数

	x_0 = bool_circ->PutFPGate(s_a, x_0, SUB, bitlen, 1); //x_0为Z

	share *x_1 = x_0;
	float two = (float)2.0;
	uint32_t *twoptr = (uint32_t *)&two;
	share *s_two = bool_circ->PutCONSGate(twoptr, bitlen);
	for (uint8_t i = 0; i < 3; i++)
	{
		x_1 = bool_circ->PutFPGate(optb, x_0, MUL, bitlen, 1);
		x_1 = bool_circ->PutFPGate(s_two, x_1, SUB, bitlen, 1);
		x_1 = bool_circ->PutFPGate(x_0, x_1, MUL, bitlen, 1);
		x_0 = x_1; //x_1为除数的倒数
	}
	share *s_out = bool_circ->PutFPGate(opta, x_1, MUL, bitlen, 1); //s_m为被除数
	//恢复操作数
	for (uint32_t i = 0; i < 8; i++)
	{
		optb->set_wire_id(23 + i, optbWires[i]);
	}
	for (uint32_t i = 0; i < 8; i++)
	{
		opta->set_wire_id(23 + i, optaWires[i]);
	}

	return s_out;
}

share *sqrt(share *opt, uint32_t bitlen, BooleanCircuit *bool_circ)
{
	share *a, *b, *tempDiv, *tempAdd;
	float zeroPointFive = 0.5F;
	uint32_t *zpfPtr = (uint32_t *)&zeroPointFive;
	share *s_zpf = bool_circ->PutCONSGate(zpfPtr, bitlen);
	a = opt;
	b = bool_circ->PutFPGate(opt, s_zpf, MUL, bitlen, 1);
	for (size_t i = 0; i < 6; i++)
	{
		a = b;
		// tempDiv = bool_circ->PutFPGate(opt, a, DIV, bitlen, 1);
		tempDiv = div(opt, a, bitlen, bool_circ);
		tempAdd = bool_circ->PutFPGate(tempDiv, a, ADD, bitlen, 1);
		b = bool_circ->PutFPGate(tempAdd, s_zpf, MUL, bitlen, 1);
	}
	return a;
}

int32_t test_circuit(e_role role, const std::string &address, uint16_t port, seclvl seclvl,
					 uint32_t numbers, uint32_t bitlen, uint32_t nthreads, e_mt_gen_alg mt_alg,
					 e_sharing sharing)
{
	ABYParty *party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg);
	std::vector<Sharing *> &sharings = party->GetSharings();
	BooleanCircuit *bool_circ = (BooleanCircuit *)sharings[S_BOOL]->GetCircuitBuildRoutine();
	float M = 94.352;
	float N = 9.2;
	// clock_t start = clock();
	uint32_t *mptr = (uint32_t *)&M;
	uint32_t *nptr = (uint32_t *)&N;

	share *s_m = bool_circ->PutCONSGate(mptr, bitlen);
	share *s_n = bool_circ->PutCONSGate(nptr, bitlen);

	// share *s_out = div(s_m, s_n, bitlen, bool_circ);
	share *s_out = sqrt(s_m, bitlen, bool_circ);

	s_out = bool_circ->PutOUTGate(s_out, ALL);
	share *s_m_t = bool_circ->PutOUTGate(s_m, ALL);
	share *s_n_t = bool_circ->PutOUTGate(s_n, ALL);

	party->ExecCircuit();

	uint32_t *s_out_out = (uint32_t *)s_out->get_clear_value_ptr();
	uint32_t *s_m_out = (uint32_t *)s_m_t->get_clear_value_ptr();
	uint32_t *s_n_out = (uint32_t *)s_n_t->get_clear_value_ptr();

	float s_out_out1 = *((float *)s_out_out);
	float s_m_out1 = *((float *)s_m_out);
	float s_n_out1 = *((float *)s_n_out);

	// std::cout << "sqrt(" << s_m_out1 << ") = " << s_out_out1 << std::endl;
	std::cout << s_m_out1 << " ÷ " << s_n_out1 << " = " << s_out_out1 << std::endl;

	delete party;
	// clock_t end = clock();
	// printf("Time: %.3Lf s\n", (long double)(end - start) / CLOCKS_PER_SEC);
	return 0;
}

int main(int argc, char **argv)
{

	e_role role;
	uint32_t bitlen = 32, numbers = 128, secparam = 128, nthreads = 1;
	uint16_t port = 7766;
	std::string address = "127.0.0.1";
	int32_t test_op = -1;
	e_mt_gen_alg mt_alg = MT_OT;
	read_test_options(&argc, &argv, &role, &bitlen, &numbers, &secparam, &address, &port, &test_op);

	seclvl seclvl = get_sec_lvl(secparam);

	test_circuit(role, address, port, seclvl, numbers, bitlen, nthreads, mt_alg, S_BOOL);

	//std::cout <<  iip << " " << verip << std::endl;
	return 0;
}
