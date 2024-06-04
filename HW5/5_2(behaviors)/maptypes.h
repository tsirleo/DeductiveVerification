#ifndef __MAPTYPES_H__
#define __MAPTYPES_H__

// Структура может хранить лишь единственное отображение для конкретного ключа. 
// Отображение представляется типом Item. 
// Его поле existent может быть истиной (то есть равняться единице) или ложью (то есть равняться нулю).
// Поле items структуры Map представляет собой массив длины capacity. 
// Поле count этой структуры определяет, сколько элементов данного массива имеет поле existent установленным в истину (единицу). 
// При работе со структурой учитываются те и только те записи массива items, которые имеют булево поле existent установленным в истину (единицу). 
// Никакие операции над структурой данных не должны приводить ее в такое состояние, чтобы после этого добавление одного отображения увеличило количество отображений более, чем на 1. 
// Иными словами, в структуре данных, все existent элементы массива должны означать отображения из хэш-таблицы.
// Отображения хранятся как последовательность пар ключ-значение в массиве items, возможно с некоторыми пропусками между ними (у пропусков поле existent установлено в ложь). 
// Элементы хранятся с начала массива. При этом за двумя последовательно идущими элементами, у которых existent установлен в ложь, остальные элементы тоже имеют existent установленным в ложь.


// Два поля размера int: key->a и key->b
typedef struct {
    int a;
    int b;
} Key;

// Два поля размера int: value->c и value->d
typedef struct {
    int c;
    int d;
} Value;

//{1} Поле existent может принимать значения 0 или 1 (false или true).
//{2} При item->existent == 0 содержимое остальных полей Item не учитывается при работе с структурой Map.
typedef struct {
    Key key __attribute__((noembed));
    Value value;
    int existent;
} Item;

//{3} Структура может хранить лишь единственное отображение для конкретного ключа (нет одинаковых ключей).
//{4} Никакие операции над структурой данных не должны приводить ее в такое состояние, чтобы после этого добавление одного отображения увеличило количество отображений более, чем на 1. 
//{5} map->items структуры Map представляет собой массив длины map->capacity. 
//{6} map->count == количеству элементов items с полем existent == 1. 
//{7} При работе со структурой учитываются те и только те записи массива items, которые имеют поле item->existent установленным в истину (item->existent == 1). 
//{8} 0 <= map->count <= map->capacity – количество "занятых" отображений меньше размера массива этих отображений. 
//{9} Отображения в map->items могут храниться с пропусками; При этом за двумя последовательно идущими элементами, у которых item->existent установлено в ложь, остальные элементы тоже имеют item->existent установленным в ложь. 
//{10} Элементы map->items хранятся с начала массива. 
typedef struct {
    Item *items;
    int capacity;
    int count;
} Map;

/*@ 
    axiomatic ItemsCount {
        logic integer count{L} (Map *map, integer m, integer n);

        axiom count_zero: 
            \forall Map *map, integer m, n; 
                (m >= n) ==> (count(map, m, n) == 0);

        predicate count_one_p{L} (Map *map, integer m) =
            count(map, m, m + 1) == (map->items[m].existent ? 1 : 0);

        axiom count_one{L}: 
            \forall Map *map, integer m; 
                count_one_p(map, m);

        predicate count_split_p{L} (Map *map, integer m, integer n, integer k) =
            count(map, m, k) == count(map, m, n) + count(map, n, k);

        axiom count_split{L}: 
            \forall Map *map, integer m, n, k; 
                (m <= n <= k) ==> count_split_p(map, m, n, k);
    }
*/

/*@ 
    logic integer all_count(Map *map) = count(map, 0, map->capacity); 
*/

/*@ 
    axiomatic CountLem {
        lemma lemma1_count_split:
            \forall Map *map, integer i;
                (is_valid_map(map) && (0 < i < map->capacity)) ==>
                    (count(map, 0, i) == count(map, 0, i - 1) + count(map, i - 1, i));

        lemma lemma2_count_split:
            \forall Map *map, integer i, j;
                (is_valid_map(map) && (0 < i < j) && (j < map->capacity)) ==>
                    (count(map, 0, j) == count(map, 0, i) + count(map, i, j));

        lemma lemma3_count_split: 
            \forall Map *map, integer m, n, k; 
                (m <= n <= k) ==> count_split_p(map, m, n, k) && (count(map, m, k) == count(map, m, n) + count(map, n, k));
        
        lemma lemma_count_one_p:
            \forall Map *map, integer i;
                is_valid_map(map) ==>
                    ((count_one_p(map, i)) && (count(map, i, (i + 1)) == ( map->items[i].existent ? 1 : 0))); 

        lemma lemma1_count_positive: 
            \forall Map *map, integer i; 
                (map->items[i].existent == 0 || map->items[i].existent == 1) ==> (count(map, i, i + 1) >= 0);
        
        lemma lemma2_count_positive:
            \forall Map *map;
                is_valid_map(map) ==> count(map, 0, map->capacity) >= 0;

        lemma lemma3_count_positive:
            \forall Map *map;
                is_valid_map(map) && (count(map, 0, map->capacity) >= 0) ==> map->count >= 0;
    }
*/

/*@
    //{1}
    predicate all_valid_existence (Map *map) =
        \forall integer i;
            (0 <= i < map->capacity) ==> (0 <= map->items[i].existent <= 1);

    //{2}
    predicate valid_item (Map *map, integer idx) =
        (0 <= idx < map->capacity) && (0 <= map->items[idx].existent <= 1);

    //{3},{4}
    predicate unique_items (Map *map) = 
        (\forall integer i; 
            (0 <= i < map->capacity) && (map->items[i].existent != 0) ==> 
                (\forall integer j; (j != i) && (0 <= j < map->capacity) && (map->items[j].existent != 0) ==> ((map->items[i].key.a != map->items[j].key.a) || (map->items[i].key.b != map->items[j].key.b))));

    //{5}
    predicate valid_items_arr_capacity (Map *map) = 
        (map->capacity > 0) && (0 <= map->count <= map->capacity) ==> \valid(map->items + (0..map->capacity - 1));

    //{6}
    predicate count_correct (Map *map) = (all_count(map) == map->count) && (map->count >= 0);

    //{7}
    predicate valid_items (Map *map) =
        \forall integer i; 
            0 <= i < map->capacity ==> valid_item(map, i);

    //{8}
    predicate valid_map_sizes (Map *map) = (0 <= map->count <= map->capacity);

    //{9}
    predicate two_consecutive_false(Map *map) =
        \exists integer i; 
            (0 <= i < map->capacity - 1) && (map->items[i].existent == 0) && (map->items[i + 1].existent == 0);

    //{9} 
    predicate rest_false_after_double(Map *map) = two_consecutive_false(map) ==> 
        (\forall integer j; 
            (0 <= j < map->capacity) &&
                (\exists integer i; 
                    (0 <= i < map->capacity - 1) && (map->items[i].existent == 0) && (map->items[i + 1].existent == 0) && i + 1 < j) ==> (map->items[j].existent == 0));

    //{10}
    predicate valid_map_begin (Map *map) = 
        (map->count > 0 ==> (map->items[0].existent == 1 || map->items[1].existent == 1)) || 
            (map->count == 0 ==> (\forall integer i; (0 <= i < map->capacity) ==> (map->items[i].existent == 0)));

    //{1}--{10}
    predicate is_valid_map (Map *map) = 
        \valid(map) && 
            all_valid_existence(map) &&
                unique_items(map) &&
                    valid_items_arr_capacity(map) &&
                        count_correct(map) &&
                            valid_items(map) &&
                                valid_map_sizes(map) &&
                                    valid_map_begin(map) &&
                                        rest_false_after_double(map);

    predicate empty_map (Map *map) = 
        (map->count == 0) &&
            (\forall integer i; (0 <= i < map->capacity) ==> map->items[i].existent == 0);
*/

#endif // __MAPTYPES_H__
