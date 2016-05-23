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
	mono while.exe ex1.whl
	mono while.exe ex2.whl
	mono while.exe ex3.whl
	mono whileref.exe ex4.whl
	mono whilesha.exe ex5.whl
	mono consha.exe ex6.csh
	mono consha.exe ex7a.csh
	mono consha.exe ex7b.csh
	mono consha.exe ex7c.csh
	mono consha.exe ex7d.csh
	mono consha.exe ex8ww.csh
	mono consha.exe ex8wr.csh
	mono consha.exe ex8rw.csh
