default: clean test

clean:
	rm -f *.dll *.mdb *.exe *.cs

Arith.exe: Arith.dfy
	dafny Arith.dfy

test: Arith.exe
	mono Arith.exe ex.arith
