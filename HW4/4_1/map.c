#include <stdlib.h>
#include <stdio.h>
#include "map.h"

int compareKeys(Key key1, Key key2) {
    return key1.a == key2.a && key1.b == key2.b;
}

int initializeMap(Map *map, int size) {
    if (size <= 0) {
        return 1;    
    }
    map->items = (Item *)malloc(size * sizeof(Item));
    if (map->items == NULL) {
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
    map->items = NULL;
}

int addElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].existent && compareKeys(map->items[i].key, *key)) {
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
    if (map->count >= 1) { 
        for (int i = 0; i < map->capacity; i++) {
            if (map->items[i].existent && (map->items[i].key.a == key->a) && (map->items[i].key.b == key->b)) {
                if (value != NULL)
                    *value = map->items[i].value;

                map->items[i].existent = 0;
                map->count--;
                foundIndex = i;

                break;
            }
        }

        if (foundIndex == -1)
            return 0;
    } else {
        return 0;
    }

    if (map->count >= 1) { 
        Key tmp_key;
        int insertIndex = foundIndex;

        for (int i = foundIndex + 1; i < map->capacity; i++) {
            if (map->items[i].existent == 1) {
                tmp_key = map->items[insertIndex].key;
                map->items[insertIndex].key = map->items[i].key;
                map->items[insertIndex].value = map->items[i].value;
                map->items[insertIndex].existent = 1;
                map->items[i].key = tmp_key;
                map->items[i].existent = 0;
                insertIndex++;
            }
        }

        return 1;
    }

    return 1;
}

int getElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].existent && compareKeys(map->items[i].key, *key)) {
            *value = map->items[i].value;
            return 1;
        }
    }
    return 0;
}
