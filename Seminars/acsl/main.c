/*
    Доки где-то были в списке литературы и на сайте frama-c.
    1) Для всех i в интервале память валидна.
    requires \forall integer i; 0 <= i < size --> \valid(arr + i);
    3, 4) Условия верификации для содержимого массива из why.
*/
/*@
    requires \valid(arr + (0..size-1));
    requires size > 0;
    ensures \forall integer i; 0 <= i < size && \old(arr[i]) == src ==> arr[i] == dst;
    ensures \forall integer i; 0 <= i < size && \old(arr[i]) != src ==> \old(arr[i]) == arr[i];
    assigns arr[0..size - 1];
    allocates \nothing;
*/
void replace(int *arr, int size, int src, int dst) {
    int *end = arr + size;
    /*@
        loop invariant end - arr >= 0;
        loop invariant \at(arr, Pre) - arr <= 0;
        loop invariant \base_addr(arr) == \base_addr(end);
        loop invariant \forall integer i; 0 <= i < (arr - \at(arr, Pre)) && \at(arr[i], Pre) == src
            ==> \at(arr, Pre)[i] == dst;
        loop invariant \forall integer i; 0 <= i < (arr - \at(arr, Pre)) && \at(arr[i], Pre) != src
            ==> \at(arr[i], Pre) == \at(arr, Pre)[i];
        loop invariant \forall integer i; (arr - \at(arr, Pre)) <= i < size ==> \at(arr[i], Pre) == \at(arr, Pre)[i];
        loop invariant \forall int *p; \base_addr(p) == \base_addr(arr) && !(\at(arr, Pre) <= p < end)
            ==> \at(*p, Pre) == *p;
        loop variant end - arr;
    */
    for (; arr < end; arr++) {
        if (*arr == src) {
            *arr = dst;
        }
    }
}