/*@
    requires \valid(a);
    requires \valid(b);
    requires *b < 10000;
    requires \base_addr(a) == \base_addr(b) ==> a != b; 
    ensures *b == \old(*b);
*/
void func(int *a, int *b) {
    *a = *b + 1;
}

/*@ 
    assigns \nothing;
*/
void caller() {
    int i = 0;
    func(&i, &i);
}