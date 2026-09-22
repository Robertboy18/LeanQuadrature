/* Exercise every supported rule and the original cosine example.
 * The Python driver checks table words, rational moments, and the example's error.
 */
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "quadrules.h"

extern double integrate(double (*f)(double), int n);
extern double integrate_testfun(void);

_Static_assert(sizeof(double) == sizeof(uint64_t), "binary64 storage is required");
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "binary64 arithmetic is required");

static uint64_t bits(double value)
{
    uint64_t result;
    memcpy(&result, &value, sizeof result);
    return result;
}

static double power(double x, int degree)
{
    double result = 1.0;
    for (int k = 0; k < degree; ++k)
        result *= x;
    return result;
}

static int current_degree;

static double monomial(double x)
{
    return power(x, current_degree);
}

int main(void)
{
    printf("cosine 2 0 %016" PRIx64 "\n", bits(integrate_testfun()));
    printf("reference 1 0 %016" PRIx64 "\n", bits(sin(1.0)));

    for (int n = 1; n <= 10; ++n) {
        for (int i = 0; i < n; ++i) {
            printf("node %d %d %016" PRIx64 "\n", n, i, bits(gauss_point(i, n)));
            printf("weight %d %d %016" PRIx64 "\n", n, i, bits(gauss_weight(i, n)));
        }
        for (int k = 0; k < 2 * n; ++k) {
            current_degree = k;
            printf("line %d %d %016" PRIx64 "\n", n, k, bits(integrate(monomial, n)));
        }
    }

    for (int d = 1; d <= 5; ++d) {
        int n = d * d;
        for (int px = 0; px < 2 * d; ++px) {
            for (int py = 0; py < 2 * d; ++py) {
                double result = 0.0;
                for (int i = 0; i < n; ++i) {
                    double point[2];
                    gauss2d_point(point, i, n);
                    result += gauss2d_weight(i, n) *
                              power(point[0], px) * power(point[1], py);
                }
                printf("square %d %d %d %016" PRIx64 "\n", n, px, py, bits(result));
            }
        }
    }

    for (int px = 0; px <= 2; ++px) {
        for (int py = 0; py <= 2 - px; ++py) {
            double result = 0.0;
            for (int i = 0; i < 3; ++i) {
                double point[2];
                hughes_point(point, i, 3);
                result += hughes_weight(i, 3) *
                          power(point[0], px) * power(point[1], py);
            }
            printf("triangle %d %d %016" PRIx64 "\n", px, py, bits(result));
        }
    }
    return 0;
}
