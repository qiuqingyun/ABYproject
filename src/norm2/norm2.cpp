#include <ENCRYPTO_utils/crypto/crypto.h>
#include <ENCRYPTO_utils/parse_options.h>
#include <ENCRYPTO_utils/thread.h>
#include <abycore/sharing/sharing.h>
#include <abycore/aby/abyparty.h>
#include <abycore/circuit/booleancircuits.h>
#include <abycore/circuit/arithmeticcircuits.h>

int32_t read_test_options(int32_t *argcp, char ***argvp, e_role *role,
                          uint32_t *bitlen, uint32_t *numbers, uint32_t *secparam, std::string *address,
                          uint16_t *port, int32_t *test_op, uint32_t *nvals, uint32_t *rands)
{
    uint32_t int_role = 0, int_port = 0;
    parsing_ctx options[] =
        {{(void *)&int_role, T_NUM, "r", "Role: 0/1", true, false},
         {(void *)numbers, T_NUM, "n", "Number of elements for inner product, default: 128", false, false},
         {(void *)bitlen, T_NUM, "b", "Bit-length, default 16", false, false},
         {(void *)secparam, T_NUM, "s", "Symmetric Security Bits, default: 128", false, false},
         {(void *)address, T_STR, "a", "IP-address, default: localhost", false, false},
         {(void *)&int_port, T_NUM, "p", "Port, default: 7766", false, false},
         {(void *)nvals, T_NUM, "v", "nvals", false, false},
         {(void *)rands, T_NUM, "x", "rands", false, false},
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

share *sqrt(share *s_number, uint32_t bitlen, BooleanCircuit *bool_circ)
{
    const float zero = 0.0F;
    const float one = 1.0F;
    const float pointFive = 0.5F;
    const float threehalfs = 1.5F;
    uint32_t shiftN = 1;       //右移位数
    uint32_t mag = 1597463007; //魔数
    //浮点数转换为32位整型表示
    uint32_t *zeroPtr = (uint32_t *)&zero;
    uint32_t *onePtr = (uint32_t *)&one;
    uint32_t *zpfPtr = (uint32_t *)&pointFive;
    uint32_t *thPtr = (uint32_t *)&threehalfs;
    //将参数输入电路
    share *s_zero = bool_circ->PutCONSGate(zeroPtr, bitlen);
    share *s_one = bool_circ->PutCONSGate(onePtr, bitlen);
    share *s_zpf = bool_circ->PutCONSGate(zpfPtr, bitlen);
    share *s_th = bool_circ->PutCONSGate(thPtr, bitlen);
    share *s_shiftN = bool_circ->PutCONSGate(shiftN, bitlen);
    share *s_mag = bool_circ->PutCONSGate(mag, bitlen);

    //判断数是否为零
    share *s_isZero = bool_circ->PutFPGate(s_number, s_zero, CMP, bitlen, 1);
    //x2=number*1.5
    share *s_x2 = bool_circ->PutFPGate(s_number, s_zpf, MUL, bitlen, 1);
    //y=number
    share *s_y = s_number;
    //由于ABY中浮点数已经是32位整型表示，因此不用进行i  = * ( long * ) &y操作
    //(y >> 1)
    share *s_shiftedR = bool_circ->PutBarrelRightShifterGate(s_y, s_shiftN);
    //0x5f3759df - ( y >> 1 )
    s_y = bool_circ->PutSUBGate(s_mag, s_shiftedR);
    //以上是将浮点数y看作32位整型进行计算，以下则是将y继续看作浮点数进行计算
    //牛顿迭代法
    for (int i = 0; i < 2; i++)
    {                                                                               //迭代两次保证精度，y  = y * ( threehalfs - ( x2 * y * y ) )
        share *s_temp_pow = bool_circ->PutFPGate(s_y, s_y, MUL, bitlen, 1);         //(y*y)
        share *s_temp_mul = bool_circ->PutFPGate(s_x2, s_temp_pow, MUL, bitlen, 1); //( x2 * y * y )
        share *s_temp_sub = bool_circ->PutFPGate(s_th, s_temp_mul, SUB, bitlen, 1); //( threehalfs - ( x2 * y * y ) )
        s_y = bool_circ->PutFPGate(s_temp_sub, s_y, MUL, bitlen, 1);                //y * ( threehalfs - ( x2 * y * y ) )
    }

    share *s_out = bool_circ->PutFPGate(s_number, s_y, MUL, bitlen, 1);
    return s_out;
}

int32_t euclid(e_role role, const std::string &address, uint16_t port, seclvl seclvl,
               uint32_t numbers, uint32_t bitlen, uint32_t nthreads, e_mt_gen_alg mt_alg, uint32_t nvals, uint32_t rands)
{
    ABYParty *party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg);
    std::vector<Sharing *> &sharings = party->GetSharings();
    Circuit *ac = (Circuit *)sharings[S_ARITH]->GetCircuitBuildRoutine();
    BooleanCircuit *bc = (BooleanCircuit *)sharings[S_BOOL]->GetCircuitBuildRoutine();
    Circuit *yc = (Circuit *)sharings[S_YAO]->GetCircuitBuildRoutine();

    //根据维数测试数字
    uint32_t a[nvals], b[nvals];
    uint32_t c = 0, d = 0;
    srand(nvals * rands);
    std::cout << "nvals: " << nvals << std::endl;
    for (int i = 0; i < nvals; i++)
    {
        a[i] = rand() % rands + 1;
        b[i] = rand() % rands + 1;
        std::cout << a[i] << " | " << b[i] << std::endl;
    }
    //计算c和d
    for (uint8_t i = 0; i < nvals; i++)
    {
        c += a[i] * a[i];
        d += b[i] * b[i];
    }
    share *s_a_simd, *s_b_simd, *s_c, *s_d;
    //输入电路
    if (role == SERVER)
    {
        s_a_simd = ac->PutSIMDINGate(nvals, a, bitlen, SERVER);
        s_b_simd = ac->PutDummySIMDINGate(nvals, bitlen);
        s_c = ac->PutINGate(c, bitlen, SERVER);
        s_d = ac->PutDummyINGate(bitlen);
    }
    else
    {
        s_a_simd = ac->PutDummySIMDINGate(nvals, bitlen);
        s_b_simd = ac->PutSIMDINGate(nvals, b, bitlen, CLIENT);
        s_c = ac->PutDummyINGate(bitlen);
        s_d = ac->PutINGate(d, bitlen, CLIENT);
    }
    //计算欧氏距离
    uint32_t zero = 0;
    share *s_fiA = ac->PutMULGate(s_a_simd, s_b_simd);

    s_fiA = ac->PutADDGate(s_fiA, s_fiA);
    share *s_split = ac->PutSplitterGate(s_fiA);
    share *s_fA = ac->PutCONSGate(zero, bitlen);
    for (uint32_t i = 0; i < nvals; i++)
        s_fA = ac->PutADDGate(s_split->get_wire_ids_as_share(i), s_fA);
    share *s_eA = ac->PutADDGate(s_c, s_d);
    s_eA = ac->PutSUBGate(s_eA, s_fA);

    s_eA = ac->PutOUTGate(s_eA, ALL);
    party->ExecCircuit();

    //恢复为明文
    uint32_t euclidDis1 = s_eA->get_clear_value<uint32_t>();

    party->Reset();

    //转换为浮点形式
    float euclidDis1F = (float)euclidDis1;
    uint32_t *euclidDisPtr = (uint32_t *)&euclidDis1F;
    share *s_euclidDis2 = bc->PutCONSGate(euclidDisPtr, bitlen);

    //开根号
    s_euclidDis2 = sqrt(s_euclidDis2, bitlen, bc);
    share *s_out = bc->PutOUTGate(s_euclidDis2, ALL);

    party->ExecCircuit();

    uint32_t *s_out_clear = (uint32_t *)s_out->get_clear_value_ptr();
    float s_out_clear_f = *((float *)s_out_clear);

    uint32_t number = 0;
    for (uint8_t i = 0; i < nvals; i++)
        number += (a[i] - b[i]) * (a[i] - b[i]);

    std::cout << "---------------------------------------" << std::endl;
    std::cout << "明文计算结果：√" << number << " = " << sqrt(number)
              << "\n安全计算结果：√" << euclidDis1 << " = " << s_out_clear_f << std::endl;
    std::cout << "---------------------------------------\n"
              << std::endl;

    delete party;
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
    uint32_t nvals = 8;
    uint32_t rands = 17;
    read_test_options(&argc, &argv, &role, &bitlen, &numbers, &secparam, &address, &port, &test_op, &nvals, &rands);

    seclvl seclvl = get_sec_lvl(secparam);

    euclid(role, address, port, seclvl, numbers, bitlen, nthreads, mt_alg, nvals, rands);
    return 0;
}
