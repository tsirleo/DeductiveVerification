#include <stdio.h>
#include <assert.h>
#include "map.h"

// Utility function to print map status for debugging
void printMapStatus(Map *map) {
    printf("Map status: capacity = %d, count = %d\n", map->capacity, map->count);
    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].existent) {
            printf("Item %d: Key = (%d, %d), Value = (%d, %d)\n", i, map->items[i].key.a, map->items[i].key.b, map->items[i].value.c, map->items[i].value.d);
        }
    }
}

// Test initialization with invalid size
void testInitializeMapInvalidSize() {
    Map map;
    int result = initializeMap(&map, 0);
    assert(result == 1);
    result = initializeMap(&map, -1);
    assert(result == 1);
    printf("testInitializeMapInvalidSize passed\n");
}

// Test initialization
void testInitializeMap() {
    Map map;
    int result = initializeMap(&map, 5);
    assert(result == 0);
    assert(map.capacity == 5);
    assert(map.count == 0);
    for (int i = 0; i < 5; i++) {
        assert(map.items[i].existent == 0);
    }
    finalizeMap(&map);
    printf("testInitializeMap passed\n");
}

// Test adding elements
void testAddElement() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    int result = addElement(&map, &key1, &value1);
    assert(result == 1);
    assert(map.count == 1);
    assert(map.items[0].existent == 1);
    assert(compareKeys(map.items[0].key, key1));
    assert(map.items[0].value.c == value1.c && map.items[0].value.d == value1.d);

    // Add another element
    Key key2 = {5, 6};
    Value value2 = {7, 8};
    result = addElement(&map, &key2, &value2);
    assert(result == 1);
    assert(map.count == 2);

    // printMapStatus(&map);

    // Try to add when map is full
    Key key3 = {9, 10};
    Value value3 = {11, 12};
    result = addElement(&map, &key3, &value3);
    assert(result == 1);
    assert(map.count == 3);  // Map should be full
    finalizeMap(&map);
    printf("testAddElement passed\n");
}

// Test adding elements to the map and reaching capacity
void testAddElementUntilFull() {
    Map map;
    initializeMap(&map, 2);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    Key key2 = {5, 6};
    Value value2 = {7, 8};
    Key key3 = {9, 10};
    Value value3 = {11, 12};

    assert(addElement(&map, &key1, &value1) == 1);
    assert(addElement(&map, &key2, &value2) == 1);
    assert(addElement(&map, &key3, &value3) == 0);  // Should fail as map is full

    finalizeMap(&map);
    printf("testAddElementUntilFull passed\n");
}

// Test adding duplicate keys
void testAddDuplicateKeys() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    Key key2 = {1, 2};  // Duplicate key
    Value value2 = {5, 6};

    assert(addElement(&map, &key1, &value1) == 1);
    assert(addElement(&map, &key2, &value2) == 1);
    assert(map.count == 1); 

    finalizeMap(&map);
    printf("testAddDuplicateKeys passed\n");
}

// Test retrieving elements
void testGetElement() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    addElement(&map, &key1, &value1);

    Value resultValue;
    int result = getElement(&map, &key1, &resultValue);
    assert(result == 1);
    assert(resultValue.c == value1.c && resultValue.d == value1.d);

    // Try to get non-existent element
    Key key2 = {5, 6};
    result = getElement(&map, &key2, &resultValue);
    assert(result == 0);
    finalizeMap(&map);
    printf("testGetElement passed\n");
}

// Test removing elements
void testRemoveElement() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    addElement(&map, &key1, &value1);

    Value resultValue;
    int result = removeElement(&map, &key1, &resultValue);
    assert(result == 1);
    assert(resultValue.c == value1.c && resultValue.d == value1.d);
    assert(map.count == 0);
    assert(map.items[0].existent == 0);

    // Try to remove non-existent element
    Key key2 = {5, 6};
    result = removeElement(&map, &key2, &resultValue);
    assert(result == 0);
    finalizeMap(&map);
    printf("testRemoveElement passed\n");
}

// Test removing all elements one by one
void testRemoveAllElements() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    Key key2 = {5, 6};
    Value value2 = {7, 8};

    addElement(&map, &key1, &value1);
    addElement(&map, &key2, &value2);

    Value removedValue;
    assert(removeElement(&map, &key1, &removedValue) == 1);
    assert(removeElement(&map, &key2, &removedValue) == 1);
    assert(map.count == 0);  // All elements removed

    finalizeMap(&map);
    printf("testRemoveAllElements passed\n");
}

// Test element removal and re-addition
void testRemoveAndReAddElement() {
    Map map;
    initializeMap(&map, 2);
    Key key1 = {1, 2};
    Value value1 = {3, 4};

    addElement(&map, &key1, &value1);

    Value removedValue;
    assert(removeElement(&map, &key1, &removedValue) == 1);

    // Re-add the same element
    assert(addElement(&map, &key1, &value1) == 1);
    assert(map.count == 1);

    finalizeMap(&map);
    printf("testRemoveAndReAddElement passed\n");
}

// Test overwriting values with same key
void testOverwriteValue() {
    Map map;
    initializeMap(&map, 3);
    Key key1 = {1, 2};
    Value value1 = {3, 4};
    Value value2 = {5, 6};

    addElement(&map, &key1, &value1);
    addElement(&map, &key1, &value2);

    Value resultValue;
    getElement(&map, &key1, &resultValue);
    assert(resultValue.c == value2.c && resultValue.d == value2.d);

    finalizeMap(&map);
    printf("testOverwriteValue passed\n");
}

// Test map with larger size
void testLargeMap() {
    int largeSize = 1000;
    Map map;
    initializeMap(&map, largeSize);

    for (int i = 0; i < largeSize; i++) {
        Key key = {i, i+1};
        Value value = {i+2, i+3};
        addElement(&map, &key, &value);
    }

    assert(map.count == largeSize);

    finalizeMap(&map);
    printf("testLargeMap passed\n");
}

// Test finalize map
void testFinalizeMap() {
    Map map;
    initializeMap(&map, 3);
    finalizeMap(&map);
    assert(map.items == NULL);
    printf("testFinalizeMap passed\n");
}

int main() {
    testInitializeMap();
    testInitializeMapInvalidSize();
    testAddElement();
    testAddElementUntilFull();
    testAddDuplicateKeys();
    testGetElement();
    testRemoveElement();
    testRemoveAllElements();
    testRemoveAndReAddElement();
    testOverwriteValue();
    testLargeMap();
    testFinalizeMap();
    printf("ALL TESTS PASSED\n");
    return 0;
}


