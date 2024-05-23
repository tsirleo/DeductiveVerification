/*@
    axiomatic Couint {
        logic integer count{L}(int *p, integer start, integer end, integer w);
        axiom count_empty{L}: \forall int *p, integer m, n, w; m >= n ==> count{L}(p, m, n, w) == 0;
        axiom count_one{L}: \forall int *p, integer m, n, w; m + 1 == n ==> count{L}(p, m, n, w) == (p[m] == w ? 1 : 0);
        axiom count_split{L}: \forall int *p, integer m, j, n, w; m <= j <= n
            ==> count{L}(p, m, n, w) == count{L}(p, m, j, w) + count{L}(p, j, n, w);
        // дробление интервалов на части довольно удобно при доказательстве.
    }
*/

/*@
    requires sz > 0;
    requires \valid(p + (0..sz-1));
    requires 0 <= idx < sz;
    ensures \old(p[idx]) == v ==> \forall integer w; count{Pre}(p, 0, sz, w) == count(p, 0, sz, w);
    // ensures \old(p[idx]) != v ==> \forall integer w; w != v /\ w != \old(p[idx]) ==> count{Pre}(p, 0, sz, w) == count(p, 0, sz, w);
    ensures \old(p[idx]) != v ==> count{Pre}(p, 0, sz, v) == count(p, 0, sz, v) - 1;
*/
void replace1(int *p, int sz, int idx, int v) {
    p[idx] = v;
    /*@
        assert count{Pre}(p, 0, idx, v) == count(p, 0, idx, v);
        assert count{Pre}(p, idx + 1, sz, v) == count(p, idx + 1, sz, v);
        assert count(p, idx, idx + 1, v) == 1; 
    */
}