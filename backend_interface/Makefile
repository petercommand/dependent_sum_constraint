all:
	g++ -Wno-unused-variable -DBINARY_OUTPUT -DBN_SUPPORT_SNARK=1 -DCURVE_BN128 -DMONTGOMERY_OUTPUT -DUSE_ASM -I../libsnark/. -I../libsnark/depends/libff -I../libsnark/depends/libfqfft  -std=c++11 -Wall -Wextra -Wfatal-errors -ggdb3 -O2 -march=native -mtune=native -O2 -g -DNDEBUG -c main.cpp -o main.o
	g++ -g main.o ../libsnark/build/libsnark/libsnark.a -lgmp -lgmpxx ../libsnark/build/depends/libff/libff/libff.a ../libsnark/build/depends/libzm.a -lcrypto -lprocps -o main
exec:
	./main ../agda/constraints_serialize ../agda/solve.result
