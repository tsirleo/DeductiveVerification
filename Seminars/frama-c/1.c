// t17 - Сишный ограниченный int. Массив - map (pointer intP) t17
/*@
    requires \valid(arr + (0..size-1));
    requires size > 0;
*/
void func(int *arr, int size) {
    arr[0] = 3;
    //@ assert arr[0] == 3;
}

/*
!!!!! После добавления func1 у func тип массива поменялся... map (pointer voidP) t17 !!!!!
В func malloc нет.
В func1 локальная переменная создаётся через malloc: int *arr = malloc(10 * sizeof(*arr)); arr[0] = 3;
А malloc возвращает void *. И смотрим мы в него указателями типа int *.
С точки зрения Java это похоже на наследование. Оно делается через tag-table. На tag'ах строится решётка.
Здесь void предок, а int потомок! И для приведений типов указателей делаются instanceof.
Поддержки side-cast (например, int * в char *) изначально не было. При переводе часть добавили, но поддержка крайне скупая.
*/

void func1() {
    int arr[10];
    arr[0] = 3;
    //@ assert arr[0] == 3; // достаточно для появления в frama-c
}