// #include <stdlib.h>
// #include <stdio.h>
// #include "map.h"

int initializeMap(Map *map, int size) {
    if (size <= 0) {
        return 1;
    }
    map->items = (Item *)malloc(size * sizeof(Item));
    if (map->items == ((void *)0)) {
        return 1;
    }

    map->capacity = size;
    map->count = 0;
    for (int i = 0; i < size; i++) {
        map->items[i].existent = 0;
    }

    return 0;
}

void finalizeMap(Map *map) {
    free(map->items);
    map->items = ((void *)0);
}

int addElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].existent && (map->items[i].key.a == key->a) && (map->items[i].key.b == key->b)) {
                map->items[i].value = *value;
                return 1;
        }
    }

    if (map->count == map->capacity) {
        return 0;
    } else {
        for (int i = 0; i < map->capacity; i++) {
            if (!map->items[i].existent) {
                map->items[i].key = *key;
                map->items[i].value = *value;
                map->items[i].existent = 1;
                map->count++;
                return 1;
            }
        }
    }

    return 0;
}

int removeElement(Map *map, Key *key, Value *value) {
    int foundIndex = -1;
    /*@ assert map->count >= 0;*/

    if (map->count >= 1) {
        /*@
            loop invariant \valid(map);
            loop invariant \valid(map->items + (0..map->capacity - 1));
            loop invariant 0 <= i <= map->capacity;
            loop invariant -1 <= foundIndex < map->capacity;
            loop invariant 0 <= map->count <= map->capacity;

            loop assigns i; 
            loop assigns *value; 
            loop assigns map->count;
            loop assigns map->items[0..map->capacity-1].existent;
            loop allocates \nothing;
            loop frees \nothing;

            loop invariant (\at(map->capacity, Pre) == \at(map->capacity, Here));
            loop invariant ((\at(value->c, Pre) == \at(value->c, Here)) && (\at(value->d, Pre) == \at(value->d, Here)));
            loop invariant count(map, 0, i + 1) == count(map, 0, i) + count(map, i, i + 1);
            loop invariant count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);
            loop invariant count(map, 0, map->capacity) == map->count;

            loop variant map->capacity - i;
        */
        for (int i = 0; i < map->capacity; i++) {
            /*@ assert map->count > 0;*/
            if (map->items[i].existent && (map->items[i].key.a == key->a) && (map->items[i].key.b == key->b)) {
                /*@ assert map->count > 0;*/
                if (value != ((void *)0)) {
                    *value = map->items[i].value;
                }
                /*@ assert map->count >= 0;*/
                /*@ assert count(map, i, i + 1) == 1;*/
                /*@ assert count(map, 0, i + 1) == count(map, 0, i) + count(map, i, i + 1);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, i + 1) + count(map, i + 1, map->capacity);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + 1 + count(map, i + 1, map->capacity);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);*/
                /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/

                map->items[i].existent = 0;
                map->count--;
                foundIndex = i;

                /*@ assert foundIndex >= 0;*/
                /*@ assert count(map, i, i + 1) == 0;*/
                /*@ assert count(map, 0, i + 1) == count(map, 0, i) + count(map, i, i + 1);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, i + 1) + count(map, i + 1, map->capacity);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + 0 + count(map, i + 1, map->capacity);*/
                /*@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);*/
                /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
                break;
            }
        }

        if (foundIndex == -1) {
            /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
            return 0;
        }
    } else {
        /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
        return 0;
    }

    /*@ assert foundIndex != -1;*/
    /*@ assert 0 <= foundIndex < map->capacity;*/
    /*@ assert 0 <= map->count <= map->capacity;*/

    if (map->count >= 1) {
        Key tmp_key;
        int insertIndex = foundIndex;
//         
        /*@ assert 0 <= insertIndex < map->capacity;*/
        /*@ assert map->count >= 0;*/

        /*@
            loop invariant \valid(map);
            loop invariant \valid(map->items + (0..map->capacity - 1));
            loop invariant 0 <= foundIndex < map->capacity;
            loop invariant foundIndex + 1 <= i <= map->capacity;
            loop invariant 0 <= map->count <= map->capacity;

            loop assigns i;
            loop assigns tmp_key;
            loop assigns insertIndex;
            loop assigns map->items[0..map->capacity - 1].value;
            loop assigns map->items[0..map->capacity-1].existent;
            loop assigns map->items[0..map->capacity - 1].key;
            loop allocates \nothing;
            loop frees \nothing;

            loop invariant (\at(map->capacity, Pre) == \at(map->capacity, Here));

            loop variant map->capacity - i;
        */
        for (int i = foundIndex + 1; i < map->capacity; i++) {
            if (map->items[i].existent == 1) {
                /*@ assert 0 <= insertIndex < map->capacity;*/
                /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/

                tmp_key = map->items[insertIndex].key;
                map->items[insertIndex].key = map->items[i].key;
                map->items[insertIndex].value = map->items[i].value;
                map->items[insertIndex].existent = 1;
                map->items[i].key = tmp_key;
                map->items[i].existent = 0;

                /*@ assert
                        \forall Key *key;
                            !has_key{Pre}(map, key) ==> !has_key{Here}(map, key);
                */
                /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
                insertIndex++;
            }
        }

        /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
        return 1;
    }

    /*@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);*/
    return 1;
}

int getElement(Map *map, Key *key, Value *value) {
    /*@
        loop invariant  0 <= i <= map->capacity;
        loop invariant is_valid_map(map);
        loop invariant map->capacity > 0;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant \at(map->capacity, Pre) == map->capacity;
        loop invariant \at(map->count, Pre) == map->count;
        loop invariant ((\at(value->c, Pre) == \at(value->c, Here)) && (\at(value->d, Pre) == \at(value->d, Here)));
        loop invariant (
            \forall integer j;
                (0 <= j < i) ==> ((map->items[j].key.a != key->a) || (map->items[j].key.b != key->b) || (map->items[j].existent != 1))
        );

        loop allocates \nothing;
        loop frees \nothing;
        
        loop variant map->capacity - i;
    */
    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].existent && (map->items[i].key.a == key->a) && (map->items[i].key.b == key->b)) {
            *value = map->items[i].value;
            /*@ assert (map->items[i].key.a == key->a);*/
            /*@ assert (map->items[i].key.b == key->b);*/
            /*@ assert (map->items[i].existent == 1);*/
            return 1;
        }

        /*@ assert ((map->items[i].key.a != key->a) || (map->items[i].key.b != key->b) || (map->items[i].existent == 0));*/
    }

    return 0;
}
