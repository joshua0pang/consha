Consha
======

Minimal imperative programming language with typed references, channels and concurrency. A simple, linear type system enables move-semantics for references and absence of data races.

The language is a research prototype inspired by [Rust](https://www.rust-lang.org/) and used for static analysis of concurrent programs, especially absence of data races with an ownership-based type system.

Verified Properties
-------------------

The language implementation includes a parser, type checker and interpreter. Everything is written in [Dafny](http://dafny.codeplex.com/) and the source code includes proofs of progress, preservation and absence of data races.

*Progress*: If program is typed and not finished, it can perform a step in the execution.

*Preservation*: If a program is typed and performs a step of execution, it remains typed.

*Absence of data races*: If the program forks a thread, the two threads cannot both access a variable concurrently if one of the accesses mutates the variable.

Language Reference
------------------

### Types

`Num` - integer

`Bool` - boolean

`Ref[Type]` - a mutable reference to a heap allocated variable of type Type.
Variable references to this type have move semantics and therefore remove the
previous variable from the scope

`Share[Type]` - an immutable reference to a heap allocated variable of type Type

### Expressions

`[num] : Num` - literal integer

`true`/`false : Bool` - boolean literals

`*(expr : Ref[T]) : T` - dereference the mutable or immutable reference computed by `expr`

`ref(expr: T) : Ref[T]` - allocate a new reference with the initial value denoted by `expr`

`share(expr: Ref[T]) : Share[T]` - convert a mutable reference to an immutable reference

`copy(expr: Share[T]) : Ref[T]` - convert an immutable reference to a (non-aliased) mutable reference

`(expr: Num + expr: Num) : Num` - add to integer expressions

`(expr: T == expr: T) : Bool` - test equality of two integer or boolean expressions

`(expr: Num > expr: Num) : Bool` - test whether the first integer expression is greater than the second integer expressions

`receive(expr: Num, Type)` - receive a value of the declared type from the channel with the numeric identifier denoted by `expr`; if there is no such value in the buffer, this expression blocks until the value is available

### Statements

`var x: Type := expr;` - declare new variable of the declared type and initialize with `expr`.

`x = expr;` - assigns a new value to the variable `x` in scope.

`*x = expr;` - if `x` is a memory reference, updates the allocated memory with a new value.

`send(expr: Num, expr: T)` - sends a value of the inferred type to the channel with the numeric identifier (this statement is non-blocking and will buffer values)

`if (expr: Bool) { statements ... } else { statements ... }` - evaluate conditional expression and continue execution with the corresponding branch

`while(expr: Bool) { statements ... }` - if the conditional expression evaluates to true, execute body and repeat until it becomes value

`fork { statements ... }` - spawns a new thread which has access to all variables in the outer scope (round-robin scheduling with a single operating system thread)

Example Programs
----------------

Summing up the first 5 integers:

```
var n: Num = 0;
var s: Num = 0;
while (6 > n) {
  s = s + n;
  n = n + 1;
}
```

Concurrent program with channels:

```
var incr: Ref[Num] = ref(0);

fork {
  var n: Num = 0;
  var res: Num = 0;
  // read incr
  var myincr: Num = *(incr);
  while (3 > n) {
    res = res + receive(1, Num) + myincr;
    n = n + 1;
  }
  send(2, res);
}

send(1, 4);
send(1, 24);
send(1, 1);

// *incr = 2;  // <-- this write is would cause a data race
               //     and is not allowed by the type system

var result: Ref[Num] = ref(receive(2, Num));
```

There are more examples in the repository.

Compiling
---------

Make sure [Dafny](http://dafny.codeplex.com/) is installed and the `dafny` executable is available in the system path.

Use `make` to create the interpreter `consha.exe`:

    $ make
