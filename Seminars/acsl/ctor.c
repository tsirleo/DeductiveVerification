#include <stdlib.h>

/* в предусловии \result ещё не было... => указать в нём не можем :(*/

/*@
    requires sz > 0;
    ensures \valid(\result + (0..sz-1));
    ensures \freeable(\result);
    ensures \allocable{Pre}(\result); // до функции ещё не выделен
    allocates \result;
*/
int *make(int sz, int v) {
    int *res = malloc(sz * sizeof(*res));
    for (int i = 0; i < sz; i++) {
        res[i] = v;
    }
    return res;
}

/*@
    requires \freeable(arr);
    ensures \allocable(arr);
    allocates arr; // разрешаем arr изменить статус, но не гарантируем его изменения
*/
void dispose(int *arr) {
    free(arr);
}