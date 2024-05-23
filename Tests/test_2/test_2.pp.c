/***************************************

Этот модуль описывает типы данных для представления
ориентированных графов, их вершин и дуг.

Граф представлен в типе `Graph`.

Поле `vertices` описывает вершины графа. Это массив из `vsize` значений
типа `Vertex`. Тип `Vertex` описывает размещение некоторой вершины графа
в массиве `vertices`. Поле `existent` в элементе массива `vertices` с
некоторым индексом `i` равно истине (т.е. не равно 0) тогда, когда в этом
элементе размещена вершина графа. В противном случае элемент массива
`vertices` с индексом `i` считается свободным.

Поле `edges` описывает дуги графа. Это массив из `esize` значений типа `Edge`.
Тип `Edge` описывает размещение некоторой дуги графа в массиве `edges`.
Поле `existent` в элементе массива `edges` имеет тот же смысл, что и то же
поле в элементе массива `vertices`. Поля `from` и `to` должны быть индексами в
массиве `vertices` и означают вершины, из которой исходит дуга и в которую
входит дуга.

Поле `ecnt` означает то количество первых элементов массива `edges`,
после которого все остальные элементы будут свободными.

Ниже приведено определение описанных типов и предикат `valid`, формально
описывающий инвариант типа `Graph`.

****************************************/


typedef struct {
    int payload;
    int existent;
} Vertex;

typedef struct {
	int from;
	int to;
	int existent;
} Edge;

typedef struct {
	Vertex *vertices;
	int vsize;
	Edge *edges;
	int ecnt;
	int esize;
} Graph;

/*@
  predicate is_vertex(Graph *g, integer v) =
  	0 <= v < g->vsize;

  predicate edge_valid(Graph *g, integer k) =
 	g->edges[k].existent ==>
	is_vertex(g, g->edges[k].from) &&
	is_vertex(g, g->edges[k].to) &&
	g->vertices[g->edges[k].from].existent &&
	g->vertices[g->edges[k].to].existent;

  predicate edges_valid(Graph *g, integer n) =
 	\forall integer k; 0 <= k < n ==> edge_valid(g, k);

  predicate graph_valid(Graph *g) =
 	g->vsize > 0 &&
    g->esize > 0 &&
    g->esize >= g->ecnt >= 0 &&
	\valid(g->vertices + (0 .. g->vsize - 1)) &&
	\valid(g->edges + (0 .. g->esize - 1)) &&
	edges_valid(g, g->ecnt) &&
	(\forall integer k; g->ecnt <= k < g->esize ==> !g->edges[k].existent);*/
// */

/*@ axiomatic EdgesCount {
    logic integer count{L}(Graph *g, integer f, integer t, integer m, integer n);

    axiom count_zero: \forall Graph *g, integer f, t, m, n; m >= n ==>
        count(g, f, t, m, n) == 0;

	predicate count_one_p{L}(Graph *g, integer f, integer t, integer m) =
        count(g, f, t, m, m + 1) == (g->edges[m].existent && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0);

    axiom count_one{L}: \forall Graph *g, integer f, t, m; count_one_p(g, f, t, m);

    predicate count_split_p{L}(Graph *g, integer f, integer t, integer m, integer n, integer k) =
        count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k);

    axiom count_split{L}: \forall Graph *g, integer f, t, m, n, k; m <= n <= k ==>
        count_split_p(g, f, t, m, n, k);
}*/

/*@ logic integer all_count(Graph *g, integer f, integer t) = count(g, f, t, 0, g->esize); */

/*@
    lemma count_zero_lemma{L}:
        \forall Graph *g, integer f, t, m, n; 
            (m >= n) ==> (count(g, f, t, m, n) == 0);

    lemma count_one_lemma{L}:
        \forall Graph *g, integer f, t, m; 
            count_one_p(g, f, t, m) && 
            (count(g, f, t, m, (m + 1)) == (g->edges[m].existent != 0 && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0));

    lemma count_split_lemma{L}: 
        \forall Graph *g, integer f, t, m, n, k; 
            (m <= n <= k) 
            ==> 
            count_split_p(g, f, t, m, n, k) && 
            (count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k));

    lemma count_split_2_lemma{L}:
        \forall Graph *g, integer f, t, m, n; 
            (m <= n) 
            ==> 
            count(g, f, t, m, (n + 1)) == count(g, f, t, m, n) + count(g, f, t, n, (n + 1));  

    lemma count_double_split_lemma{L}:
        \forall Graph *g, integer f, t, m, n, k; 
            (m <= k <= n - 1) 
            ==> 
            (count(g, f, t, m, n) == count(g, f, t, m, k) + count(g, f, t, k, (k + 1)) + count(g, f, t, (k + 1), n));

    lemma all_count_lemma{L}: 
        \forall Graph *g, integer k, f, t;
            (0 <= g->ecnt <= g->esize) 
            ==> 
            (all_count(g, f, t) == count(g, f, t, 0, g->esize)) &&
            (all_count(g, f, t) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize)) &&
            (count(g, f, t, 0, g->esize) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize));

    lemma zero_after_ecnt_lemma{L}: 
        \forall Graph *g, integer f, t, m;
            graph_valid(g) ==> 
            (g->ecnt <= (m - 1) < g->esize) ==> 
            (count(g, f, t, (m - 1), m) == 0) && (g->edges[m - 1].existent == 0);

    lemma count_lemma{L}: 
        \forall Graph *g, integer f, t, m;
            (0 <= (m - 1) <= g->ecnt) ==> 
            (count(g,f, t, 0, m) == count(g, f, t, 0, (m - 1)) + count(g, f, t, (m - 1), m));
*/
// */

/*@
    ghost
    /@
        lemma
        requires \valid(g);
        requires graph_valid(g);
        requires g->ecnt <= k <= g->esize;
        decreases k - g->ecnt;
        ensures count(g, f, t, g->ecnt, k) == 0;
    @/
    void count_not_existent_lemma(Graph *g, int f, int t, int k) {
        if (k > g->ecnt) {
            //@ assert count(g, f, t, (k - 1), k) == 0;
            //@ assert count(g, f, t, g->ecnt, k) == count(g, f, t, g->ecnt, (k - 1)) + count(g, f, t, (k - 1), k); 
            count_not_existent_lemma(g, f, t, (k - 1));
        }
    }
        */
// */


/*@
  requires \valid(g) && graph_valid(g);
  requires is_vertex(g, f);
  requires is_vertex(g, t);
  requires g->vertices[f].existent;
  requires g->vertices[t].existent;
  ensures \valid(g);
  ensures graph_valid(g);
  ensures all_count(g, f, t) == 0;
  ensures \forall integer f2, t2; (f2 != f || t2 != t) ==> all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);*/
// */
void
remove_edge(Graph *g, int f, int t)
{
    int c = 0;
    Before:

    /*@ 
        loop invariant i >= 0;
        loop invariant i <= g->ecnt;
        loop invariant c >= 0;
        loop invariant c <= g->esize;

        loop invariant graph_valid(g);

        loop invariant count(g, f, t, 0, i) == 0;
      
        loop invariant \forall integer f2, t2; 
            (f2 != f || t2 != t) ==> 
                all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);

        loop invariant \forall integer k; i <= k < g->esize ==> g->edges[k].existent == \at(g->edges[k].existent, Before);

        loop invariant count(g, f, t, i, g->esize) == count{Before}(g, f, t, i, g->esize);
        
        loop invariant \forall integer m; 0 <= m < i ==> g->edges[m].from == f ==> g->edges[m].to == t ==> !g->edges[m].existent;

        loop invariant \forall integer k;
                (c <= k < i)
                ==>
                (!g->edges[k].existent);
        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        /*@ assert \valid(g);*/
        /*@ assert graph_valid(g);*/

        Pre1:

        if (g->edges[i].from == f && g->edges[i].to == t) {
//             
	        g->edges[i].existent = 0;

            /*@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, i, i + 1) == count{Before}(g, f2, t2, i, i + 1);*/
            /*@ assert count(g, f, t, i, i + 1) == 0;*/
            /*@ assert \forall integer m; 0 <= m < i ==> g->edges[m].from == f ==> g->edges[m].to == t ==> \at(!g->edges[m].existent, Here);*/
            /*@ assert \forall integer m; 0 <= m < i ==> g->edges[m].from == f ==> g->edges[m].to == t ==> \at(!g->edges[m].existent, Pre1);*/
//             
            /*@ ghost
                int l = 0;
                /@
                    loop invariant l >= 0;
                    loop invariant l <= g->esize;
                    loop invariant \valid(g);
                    loop invariant \valid(g->edges + (0 .. g->esize - 1));
                    loop invariant graph_valid(g);

                    loop invariant \forall integer j;
                        (0 <= j < l) && (j != i) ==>
                            count{Pre1}(g, f, t, j, (j + 1)) == count{Here}(g, f, t, j, (j + 1)); 
                    
                    loop invariant (l <= i - 1) ==> 
                        count{Pre1}(g,f,t, 0, l + 1) == count{Pre1}(g, f, t, 0, l) + count{Pre1}(g, f, t, l, l + 1);

                    loop invariant (l <= i - 1) ==> 
                        count{Here}(g,f,t, 0, l + 1) == count{Here}(g, f, t, 0, l) + count{Here}(g, f, t, l, l + 1);
                    
                    loop invariant (l <= i) ==>
                            count{Pre1}(g, f, t, 0, l) == count{Here}(g, f, t, 0, l); 

                    loop invariant (l > i - 1) ==> 
                        count{Pre1}(g, f, t, 0, l + 1) == count{Pre1}(g, f, t, 0, l) + count{Pre1}(g, f, t, l, l + 1);

                    loop invariant (l > i - 1) ==> 
                            count{Here}(g, f, t, 0, l + 1) == count{Here}(g, f, t, 0, l) + count{Here}(g, f, t, l, l + 1);

                    loop invariant \forall integer j;
                    (0 <= j <= l - 1) ==>
                        \forall integer f2, t2;
                            (f2 != f || t2 != t) ==>
                                count{Pre1}(g, f2, t2, 0, j + 1) == 
                                    count{Pre1}(g, f2, t2, 0, j) + count{Pre1}(g, f2, t2, j, j + 1);
                
                    loop invariant \forall integer j;
                        (0 <= j && j >= l - 1 && j < g->esize) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>
                                    count{Pre1}(g, f2, t2, 0, j + 1) == 
                                        count{Pre1}(g, f2, t2, 0, j) + count{Pre1}(g, f2, t2, j, j + 1);

                    loop invariant \forall integer j;
                        (0 <= j <= l - 1) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>
                                    count{Here}(g, f2, t2, 0, j + 1) == 
                                        count{Here}(g, f2, t2, 0, j) + count{Here}(g, f2, t2, j, j + 1);
                    
                    loop invariant \forall integer j;
                        (0 <= j && j >= l - 1 && j < g->esize) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>
                                    count{Here}(g, f2, t2, 0, j + 1) == 
                                        count{Here}(g, f2, t2, 0, j) + count{Here}(g, f2, t2, j, j + 1);

                    loop invariant \forall integer j;
                        (0 <= j <= l - 1) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>
                                    count{Here}(g, f2, t2, j, j + 1) == 
                                        count{Pre1}(g, f2, t2, j, j + 1);

                    loop invariant \forall integer j;
                        (0 <= j <= l) ==>
                            \forall integer f2, t2;
                                (f2 != f || t2 != t) ==>
                                    count{Here}(g, f2, t2, 0, j) == 
                                        count{Pre1}(g, f2, t2, 0, j);
                    
                    loop invariant \forall integer k;
                        (c <= k < i)
                        ==>
                        (!g->edges[k].existent);

                    loop assigns \nothing;
                    loop variant g->esize - l;
                
                @/
                while (l < g->esize) {
                    ++l;
                    //@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, l - 1, l) ==  count{Pre1}(g, f2, t2, l - 1, l);
                    //@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, l) ==  count{Here}(g, f2, t2, 0, l - 1) + count{Here}(g, f2, t2, l - 1, l);
                    //@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Pre1}(g, f2, t2, 0, l) ==  count{Pre1}(g, f2, t2, 0, l - 1) + count{Pre1}(g, f2, t2, l - 1, l);
                    //@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, l - 1) ==  count{Pre1}(g, f2, t2, 0, l - 1);
                    //@ assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, l) ==  count{Pre1}(g, f2, t2, 0, l - 1) + count{Pre1}(g, f2, t2, l - 1, l);
                }

                
            */

            /*@ ghost
                /@
                    loop invariant 0 <= h <= i;
                    loop invariant \forall integer m; 0 <= m < i ==> g->edges[m].from == f ==> g->edges[m].to == t ==> \at(!g->edges[m].existent, Here);
                    loop invariant \forall integer m; 0 <= m < i ==> g->edges[m].from == f ==> g->edges[m].to == t ==> \at(!g->edges[m].existent, Pre1);
                    loop invariant count{Here}(g, f, t, 0, h) == count{Pre1}(g, f, t, 0, h);
                    loop variant i - h;
                @/
                for (int h = 0; h < i; ++h) {
                    //@ assert count{Here}(g, f, t, 0, h + 1) == count{Here}(g, f, t, 0, h) + count{Here}(g, f, t, h, h + 1);
                    //@ assert count{Pre1}(g, f, t, 0, h + 1) == count{Pre1}(g, f, t, 0, h) + count{Pre1}(g, f, t, h, h + 1);
                }
            */

            /*@ ghost
                /@
                    loop invariant i + 1 <= h <= g->esize;
                    loop invariant \forall integer m; i + 1 <= m < g->esize ==> g->edges[m].from == f ==> g->edges[m].to == t ==> 
                        \at(g->edges[m].existent, Before) == \at(g->edges[m].existent, Here);
                    loop invariant count(g, f, t, i + 1, h) == count{Before}(g, f, t, i + 1, h);
                    loop variant g->esize - h;
                @/
                for (int h = i + 1; h < g->esize; ++h) {
                    //@ assert count{Here}(g, f, t, i + 1, h + 1) == count{Here}(g, f, t, i + 1, h) + count{Here}(g, f, t, h, h + 1);
                    //@ assert count{Before}(g, f, t, i + 1, h + 1) == count{Before}(g, f, t, i + 1, h) + count{Before}(g, f, t, h, h + 1);
                }
            */
            // loop invariant count(g, f, t, i, g->esize) == \at(count(g, f, t, i, g->esize), Before);

            /*@ assert count{Here}(g, f, t, 0, i) == count{Pre1}(g, f, t, 0, i);*/
            /*@ assert count(g, f, t, 0, i + 1) == count(g, f, t, 0, i) + count(g, f, t, i, i + 1);*/
            /*@ assert count(g, f, t, 0, i + 1) == 0;*/
            /*@ assert c >= 0;*/
        }
        if (g->edges[i].existent) {
            Pre2:
            /*@ assert i >= 0;*/
            /*@ assert c >= 0;*/
            c = i + 1;
            /*@ assert c >= 0;*/
//             
            /*@ assert c <= g->ecnt;*/

        }

        /*@ assert c >= 0;*/
    }
    /*@ assert \valid(g);*/
    /*@ assert graph_valid(g);*/
    /*@ assert c >= 0;*/
    /*@ assert \forall integer k; c <= k < g->ecnt ==> g->edges[k].existent == 0; // from c to old ecnt all edges[].existent == 0
*/    g->ecnt = c;
    /*@ assert g->esize >= g->ecnt >= 0;*/
    /*@ assert edges_valid(g, g->ecnt);*/
    /*@ assert graph_valid(g);*/
}
// 
