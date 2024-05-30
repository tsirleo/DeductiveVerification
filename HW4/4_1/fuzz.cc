#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "map.h"

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < sizeof(Key) + sizeof(Value) + sizeof(int)) {
        return 0;
    }

    Map map;
    initializeMap(&map, 10);

    Key key;
    Value value;

    memcpy(&key, data, sizeof(Key));
    memcpy(&value, data + sizeof(Key), sizeof(Value));
    int operation = *(int *)(data + sizeof(Key) + sizeof(Value));

    switch (operation % 3) {
        case 0:
            addElement(&map, &key, &value);
            break;
        case 1:
            removeElement(&map, &key, &value);
            break;
        case 2:
            getElement(&map, &key, &value);
            break;
    }

    finalizeMap(&map);
    return 0;
}

