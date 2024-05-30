SOURCE=map.c test.c
TARGET=test

CFLAGS = -I. -Wall -Wextra -std=c99

all: $(TARGET)

$(TARGET): $(SOURCE)
	gcc $(CFLAGS) -o $@ -I. $^

run_tests: all
	./$(TARGET)

clean:
	rm -rf $(TARGET)

static: $(SOURCE)
	cppcheck --enable=all --check-config --std=c99 $(SOURCE)

sanitize: $(SOURCE)
	gcc $(CFLAGS) -fsanitize=undefined,address -o $(TARGET) $^
	./$(TARGET)

dynamic: $(SOURCE)
	gcc $(CFLAGS) -g -o $(TARGET) $^
	valgrind ./$(TARGET)

coverage: $(SOURCE)
	gcc $(CFLAGS) --coverage -o $(TARGET) $^
	valgrind ./$(TARGET) --track-origins=yes -s
	lcov -t "$(TARGET)" -o $(TARGET).info -c -d .
	genhtml -o $(TARGET)-lcov-report $(TARGET).info
	open test-lcov-report/index.html

fuzzer:
	clang++ -fsanitize=fuzzer,address -o fuzz fuzz.cc map.c -I.
	mkdir -p fuzz_input
	echo "" > fuzz_input/seed
	./fuzz -runs=100000000 fuzz_input


clean_all:
	rm -rf $(TARGET) $(TARGET).gcno $(TARGET).gcda $(TARGET).info $(TARGET)-lcov-report fuzz_input fuzz
	rm -rf *.gcno *.gcda
