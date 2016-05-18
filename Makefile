default: clean while.exe

clean:
	rm -f *.dll *.mdb *.exe while.cs

while.exe: while.dfy ReadFileNative.cs
	dafny while.dfy ReadFileNative.cs

test: while.exe
	mono while.exe ex1.whl
	mono while.exe ex2.whl
	mono while.exe ex3.whl
