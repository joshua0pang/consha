default: clean while.exe

clean:
	rm -f *.dll *.mdb *.exe while.cs whileref.cs whilesha.cs consha.cs

while.exe: while.dfy ReadFileNative.cs
	dafny while.dfy ReadFileNative.cs

whileref.exe: whileref.dfy ReadFileNative.cs
	dafny whileref.dfy ReadFileNative.cs

whilesha.exe: whilesha.dfy ReadFileNative.cs
	dafny whilesha.dfy ReadFileNative.cs

test: while.exe whileref.exe whilesha.exe
	mono while.exe ex1.whl
	mono while.exe ex2.whl
	mono while.exe ex3.whl
	mono whileref.exe ex4.whl
	mono whilesha.exe ex5.whl
