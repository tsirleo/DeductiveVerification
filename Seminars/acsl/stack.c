#include <stdlib.h>

void func(int *p, int *k, int q) {}

/*@
    assigns \nothing;
*/
void caller() {
    int i = 0;
    int *k = malloc(sizeof(*k));
    *k = 10;
    int j = 42;
    func(&i, k, j);
}