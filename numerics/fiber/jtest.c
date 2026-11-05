#include <stdio.h>
#include <stdlib.h>
#include "fibcore.h"
int main(int argc, char **argv)
{
    slong prec = 128; fib_init(prec);
    arb_t c, J, d; arb_init(c); arb_init(J); arb_init(d); arb_struct a[4]; for (int k = 0; k < 4; k++) arb_init(a + k);
    arb_set_str(c, argv[1], prec);
    arb_t n; arb_init(n); arb_zero(n);
    for (int k = 0; k < 4; k++) { arb_set_str(a + k, argv[2 + k], prec); arb_addmul(n, a + k, a + k, prec); }
    arb_sqrt(n, n, prec); for (int k = 0; k < 4; k++) arb_div(a + k, a + k, n, prec);
    int f = Jfun(J, c, a, prec); dfun(d, c, prec);
    printf("fail=%d J = ", f); arb_printd(J, 15); printf("   d = "); arb_printd(d, 15); printf("\n");
    return 0;
}
