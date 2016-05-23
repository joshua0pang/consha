default: clean while.exe

clean:
	rm -f *.dll *.mdb *.exe while.cs whileref.cs whilesha.cs consha.cs

while.exe: while.dfy ReadFileNative.cs
	dafny while.dfy ReadFileNative.cs

whileref.exe: whileref.dfy ReadFileNative.cs
	dafny whileref.dfy ReadFileNative.cs

whilesha.exe: whilesha.dfy ReadFileNative.cs
	dafny whilesha.dfy ReadFileNative.cs

consha.exe: consha.dfy ReadFileNative.cs
	dafny consha.dfy ReadFileNative.cs

test: while.exe whileref.exe whilesha.exe consha.exe
	mono while.exe examples/ex1.whl
	mono while.exe examples/ex2.whl
	mono while.exe examples/ex3.whl
	mono whileref.exe examples/ex4.whl
	mono whilesha.exe examples/ex5.whl
	mono consha.exe examples/ex6.csh
	mono consha.exe examples/ex7a.csh
	mono consha.exe examples/ex7b.csh
	mono consha.exe examples/ex7c.csh
	mono consha.exe examples/ex7d.csh
	mono consha.exe examples/ex8ww.csh
	mono consha.exe examples/ex8wr.csh
	mono consha.exe examples/ex8rw.csh
