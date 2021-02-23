#include <iostream>
#include <ctime>
#include <cmath>
using namespace std;
float reciprocal(float x)
{
    float z = 2.8235294 - 1.8823529 * x;
    for (size_t i = 0; i < 8; i++)
    {
        z = z + z * (1 - x * z);
        printf("z:%f\n", z);
    }
    return z;
}
float Q_rsqrt(float number)
{
    long i;
    float x2, y;
    const float threehalfs = 1.5F;

    x2 = number * 0.5F;
    y = number;
    i = *(long *)&y;           // evil floating point bit level hacking
    i = 0x5f3759df - (i >> 1); // what the fuck?
    y = *(float *)&i;
    y = y * (threehalfs - (x2 * y * y)); // 1st iteration
                                         //	y  = y * ( threehalfs - ( x2 * y * y ) );   // 2nd iteration, this can be removed

    return reciprocal(y);
}
float rsqrt(float number)
{
    long i;
    float x2, y;
    const float threehalfs = 1.5F;

    x2 = number * 0.5F;
    y = x2;
    y = y * (threehalfs - (x2 * y * y)); // 1st iteration
    printf("y: %f\n", y);
    return 1 / y;
}
float sqrts(float x)
{
    float a, b;
    a = x;
    b = x * 0.5;
    for (size_t i = 0; i < 4; i++)
    {
        a = b;
        b = 0.5 * (a + x / a);
    }
    return a;
}
typedef union
{
    float f;
    struct
    {
        unsigned int mantisa : 23;
        unsigned int exponent : 8;
        unsigned int sign : 1;
    } parts;
} float_cast;
int main()
{
    // cout << "input x: " << flush;
    float x, ans;
    // cin >> x;
    // x = 0.04;
    float_cast d1 = {.f = 94.352};
    printf("sign = %x\n", d1.parts.sign);
    printf("exponent = %x\n", d1.parts.exponent);
    printf("mantisa = %x\n", d1.parts.mantisa);
    // clock_t start = clock();
    // ans = Q_rsqrt(x);
    // ans = rsqrt(x);
    // ans = sqrts(x);
    // ans=reciprocal(x);
    // clock_t end = clock();
    // printf("\nAnswer: %.4f\ncheck: %.4f\n", ans, sqrt(x));
    // printf("Time: %.3Lf ms\n", (long double)(end - start) / CLOCKS_PER_SEC * 1000);
    return 0;
}