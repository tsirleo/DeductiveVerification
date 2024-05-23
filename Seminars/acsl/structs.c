typedef struct S {
    int a;
    int b;
} S;

/*@
    requires \valid(s);
    requires s->b > 0; 
    ensures s->a > 0;
*/
void func(S *s) {
    s->a = 42;
}