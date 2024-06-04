#ifndef __MAP_H__
#define __MAP_H__

#include "maptypes.h"

/*@
    predicate full{L} (Map *map) = (\at(map->capacity, L) == \at(map->count, L));

    predicate has_key{L} (Map *map, Key *key) =
        \exists integer i; 
            (0 <= i < \at(map->capacity, L)) && (\at(map->items[i].existent, L) == 1) && (\at(map->items[i].key.a, L) == key->a) && (\at(map->items[i].key.b, L) == key->b);

    predicate has_item{L1, L2} (Map *map, Key *key, Value *value) =
        \exists integer i; 
            (0 <= i < \at(map->capacity, L1)) && (\at(map->items[i].existent, L1) != 0) && 
                (\at(map->items[i].key.a, L1) == \at(key->a, L2)) && (\at(map->items[i].key.b, L1) == \at(key->b, L2)) &&
                    (\at(map->items[i].value.c, L1) == \at(value->c, L2)) && (\at(map->items[i].value.d, L1) == \at(value->d, L2));

    predicate item_exists_t {L} (Item *it) = \at(it->existent, L)  == 1; 

    logic Key* get_key_t {L} (Item *it) = \at(&it->key, L);

    logic Value* get_value_t {L} (Item *it) = \at(&it->value, L);

    logic Item* get_item_t {L} (Map *map, integer idx) = \at(&map->items[idx], L);
*/

/*
    allocates \nothing;
    frees \nothing;
    ensures key1.a == key2.a && key1.b == key2.b ==> (\result == 1);
    ensures key1.a != key2.a || key1.b != key2.b ==> (\result == 0);  
*/
int compareKeys(Key key1, Key key2);

int initializeMap(Map *map, int size);

//{1} Функция finalizeMap() освобождает динамическую память, используемую для ассоциативного массива map.
//{2} На вход функции должен подаваться указатель на область памяти, проинициализированную функцией initializeMap(). 
/*@
    requires is_valid_map(map);   //{2}
    requires \freeable(map->items);   //{2}
    ensures \allocable(\old(map->items));   //{1}
*/
void finalizeMap(Map *map);

int addElement(Map *map, Key *key, Value *value);

//{1} Функция removeElement() удаляет сохранённое в ассоциативном массиве map значение по заданному ключу key (если оно там было). 
//{2} Функция не удаляет другие отображения, кроме отображения по заданному ключу,
//{3} а также не добавляет новые отображения. 
//{4} Функция возвращает истину (единицу), если функция изменила ассоциативный массив, ложь (ноль) в противном случае. 
//{5} В случае, если значение было удалено и при этом переданный указатель value был отличен от нулевого, функция записывает значение, содержавшееся для заданного ключа, по данному указателю. 
//{6} Функция имеет право изменять структуру ассоциативного массива, если это не отражается на содержащихся в нём парах. 
//{7} Ничего другого функция не делает.
/*@
    requires map != \null;
    requires key != \null;
    requires \valid(key);   //требования к типу данных
    requires \valid(value);   //требования к типу данных
    requires is_valid_map(map);   //требования к типу данных
    requires map->capacity > 0;

    allocates \nothing;    //{7}
    frees \nothing;   //{7}
    assigns *value;   //{5}
    assigns map->count;   //{1}
    assigns map->items[0..map->capacity - 1].value;   //{6}
    assigns map->items[0..map->capacity-1].existent;   //{6}
    assigns map->items[0..map->capacity - 1].key;   //{6} 

    ensures \valid(key);
    ensures \valid(map);
    ensures is_valid_map(map);
    ensures (\valid(value) || value == \null);
    ensures (map->capacity == \old(map->capacity));    //{7}
    ensures !has_key{Pre}(map, key) ==> (\result == 0) ==> (\old(map->count) == map->count) && (count(\old(map), 0, \old(map->capacity)) == count(map, 0, map->capacity));   //{1},{4}
    ensures has_key{Pre}(map, key) ==> (\result == 1) ==> (\old(map->count) == map->count + 1) && (count(\old(map), 0, \old(map->capacity)) == count(map, 0, map->capacity) + 1);   //{1},{4}
    ensures has_key{Pre}(map, key) ==> (\result == 1) ==> 
        \exists integer i; 
            (0 <= i < map->capacity) && (\old(map->items[i].key.a) == key->a) && (\old(map->items[i].key.b) == key->b) && (\old(map->items[i].existent) == 1) &&
                (\exists integer j;
                    (0 <= j < map->capacity) && (map->items[j].existent == 0) && (map->items[j].key.a == key->a) && (map->items[j].key.b == key->b));   //{1},{4}
    ensures \forall integer i;
        (0 <= i < map->capacity) && ((\old(map->items[i].key.a) != key->a) || (\old(map->items[i].key.b) != key->b)) && (\old(map->items[i].existent) == 1) && 
            (\exists integer j;
                (0 <= j < map->capacity) && (\old(map->items[i].key.a) == map->items[j].key.a) && (\old(map->items[i].key.b) == map->items[j].key.b) && (\old(map->items[i].existent) == map->items[j].existent));   //{2}
    ensures \forall Key *key;
        !has_key{Pre}(map, key) ==> !has_key{Post}(map, key);   //{3}
    ensures (\result == 0) ==> (value == \old(value));   //{5}
    ensures (\result == 1) && (\old(value) == \null) ==> (*value == \old(*value));   //{5}
    ensures (\result == 1) && (\old(value) != \null) ==> 
        (\exists integer i; 
            (0 <= i < \old(map->capacity)) && (\old(map->items[i].value.c) == value->c) && (\old(map->items[i].value.d) == value->d));   //{5}
*/
int removeElement(Map *map, Key *key, Value *value);

//{0} Функция getElement() возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key  
//{1} и возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа.
//{2} В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит. 
//{3} Функция не меняет ассоциативный массив. 
//{4} Функция не меняет переданный ключ. 
//{5} Ничего другого функция не делает. 
/*@
    requires map != \null;
    requires key != \null;
    requires \valid(key);   //требования к типу данных
    requires \valid(value);   //требования к типу данных
    requires is_valid_map(map);   //требования к типу данных
    requires map->capacity > 0;

    allocates \nothing;   //{5}
    frees \nothing;   //{5}
    assigns *value;   //{0}

    ensures has_key{Pre}(map, key) ==> (\result == 1);   //{1}
    ensures !has_key{Pre}(map, key) ==> (\result == 0) && (value == \old(value));   //{2}
    ensures \old(map->capacity) == map->capacity;   //{3}
    ensures \old(map->count) == map->count;   //{3}
    ensures \forall integer i;
        (0 <= i < map->capacity) ==> ((map->items[i].existent == \old(map->items[i].existent)) && 
            (map->items[i].key.a == \old(map->items[i].key.a)) && (map->items[i].key.b == \old(map->items[i].key.b)) && 
                (map->items[i].value.c == \old(map->items[i].value.c)) && (map->items[i].value.d == \old(map->items[i].value.d)));   //{3}
    ensures key == \old(key);    //{4}
    ensures is_valid_map(map);   //{3},{5} - требования к типу данных
*/
int getElement(Map *map, Key *key, Value *value);

#endif // __MAP_H__

