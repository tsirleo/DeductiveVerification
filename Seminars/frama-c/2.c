struct Key {
    int a;
    int b;
};

struct Value {
    int c;
    int d;
};

struct Item {
    struct Key key __attribute__((noembed));
    struct Value value;
};

// Вложенных структур в Java тоже не было => value превращается в ссылку.
// Разные поля раскиданы по memory, но не алиасятся, а одинаковые нужно руками разделить.

/*@
    requires \valid(items + (0..size-1));
    requires size >= 2;
    requires \forall integer k, l; 0 <= k < l < size ==> &(items[k].value) != &(items[l].value); // а теперь поймёт, что алиасов нет.
*/
void func(struct Item *items, int size) {
    items[0].value.c = 42;
    items[1].value.c = 13;
    //@ assert items[0].value.c == 42;
}

// Ещё есть ядерный макрос container_of, позволяющий из вложенной структуры получить адрес внешней.
// Получается через примерно такую аксиому:
// (struct Item*)((char *)&i->value-8)==i, где 8 - offset_of value в Item.
// Тогда из совпадения адресов value будет следовать совпадение адресов i1 и i2.
// Нам с этим возиться не потребуется: технически сложнее.

// А для первой вложенной структуры ничего делать не нужно: эксплуатируется наследование!
// Но если поле перед ним добавить, фокус пропадёт.
// Проблема: модифицируем Item, модифицируя Key!
/*@
    requires \valid(items + (0..size-1));
    requires size >= 2;
*/
void func2(struct Item *items, int size) {
    items[0].key.a = 42;
    items[1].key.a = 13;
    //@ assert items[0].key.a == 42;
}

// Ещё проблема: при явном приведении Item * к Key * он видит downcast и начинает всё типизировать "предком" Key.
// В Java все элементы массива обязаны быть одного типа, задаваемого при создании: примитивного или указательного.
// items[1].key.a → (items + 1)->key.a → ((Key *)(items + 1))->a
//                                                \ Item  /
// ∀ Item *i; (Key *)i ≡ i => проблема:
// А значит инструмент оптимизирует в (items + 1)->a≡((Key *)items + 1)->a => неправильное смещение в массиве.
// Для "отклеивания" Key от Item есть __attribute__((noembed))
// Теперь каст к Key * и func2 сломается.
// В Java указателей внутрь массива нет: только индексация.
/*@
    requires \valid(items + (0..size-1));
    requires size >= 2;
*/
void func3(struct Item *items, int size) {
    // struct Key *k = (struct Key *) items; // с noembed так теперь нельзя.
    items[0].key.a = 42;
    items[1].key.a = 13;
    //@ assert items[0].key.a == 42;
}

// Не всё, что может/не может инструмент есть даже в головах разработчиков. В случае чего пишем Евгению Валерьевичу.