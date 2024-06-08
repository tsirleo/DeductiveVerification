// #include <limits.h>

/*@
    requires sz >= 0;
    requires x < 0x7fffffff;
    requires \valid(a + (0..sz-1));
    
    assigns a[0..sz-1];
    frees \nothing;
    allocates \nothing;

    ensures \valid(a + (0..sz-1));
    ensures (
        \forall integer i;
            (0 <= i < \old(sz)) && (\old(*(\old(a) + i)) == x) ==> (*(\old(a) + i) == (x + 1))
    );

    ensures (
        \forall integer i;
            (0 <= i < \old(sz)) && (\old(*(\old(a) + i)) != x) ==>
                    ((\old(*(\old(a) + i))) == (*(\old(a) + i)))
    );*/
// */
void xinc(int *a, int sz, int x)
{
    /*@ ghost
        int size = sz;
        int *pre_a = a;
        int l = 0;
    */
    /*@
        loop invariant sz >= 0;
        loop invariant sz <= size;
        loop invariant l >= 0;
        loop invariant l <= size;
        loop invariant l == a - \at(a, Pre);
        loop invariant a == pre_a + size - sz;
        loop invariant \forall integer i; 
            ((0 <= i < size - \at(sz, Here)) && 
                (\at(*(\at(a, Pre) + i), Pre) == x)) ==>
                    (*(\at(a, Pre) + i) == (x + 1));

        loop invariant \forall integer i; 
            ((0 <= i < size - \at(sz, Here)) && 
                (\at(*(\at(a, Pre) + i), Pre) != x)) ==> 
            (
                (\at(*(\at(a, Pre) + i), Pre)) ==
                    (\at(*(\at(a, Pre) + i), Here))
            );

        loop invariant (
            \forall integer i;
                (l <= i <= size) ==>
                    *(\at(a, Pre) + i) == \at(*(a + i), Pre)
        );

        loop variant sz;
    */
    while (sz--) {
        /*@ assert *a == *(\at(a, Pre) + l);*/
        /*@ assert *a == \at(\at(a, Pre)[\at(l, Here)], Pre);*/
        if (*a == x) {
            ++*a;
        }
//         
        /*@ ghost */
        ++a;
        /*@ ghost
            ++l;
        */
    }
}

/*@ ensures \result; */
int test1(void)
{
    int a1[] = {1, -1, 1, 3};
    xinc(&a1[0], 4, 1);
    return a1[0] == 2
        && a1[1] == -1
        && a1[2] == 2
        && a1[3] == 3;
}

/*@ ensures \result; */
int test2(void)
{
    int a2[] = {10, 10, 10};
    xinc(&a2[1], 1, 10);
    return a2[0] == 10
        && a2[1] == 11
        && a2[2] == 10;
}
