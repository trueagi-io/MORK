# Basics

## Keeping Things Separate

We have two `.mm2` files. 

`Basics_file1.mm2`
```
a
b
```

`Basics_file2.mm2`
```
b
c
```

We decide to manually concatenate them to have the contents of both files

`Basics_file1_file2.mm2`
```
; from `Basics_file1.mm2`
a
b

; from `Basics_file2.mm2`
b
c
```
run `./mork run Basics_file1_file2.mm2` 

we get:
```
a
b
c
```
So we can see that this constitutes a _set union_ over the expressions in the file.

This may be the desired behavior, but often one would like to ensure that the separate files behave as separate sets.
This would require a form of _predication_.

We can do this simply by adding a prefix.
`Basics_file1_file2_predicated.mm2`
```
; from `Basics_file1.mm2`
(file1 a)
(file1 b)

; from `Basics_file2.mm2`
(file2 b)
(file2 c)
```
run `./mork run Basics_file1_file2_predicated.mm2` 
We still end up with a set union, but they remain disjoint.
```
(file1 a)
(file1 b)
(file2 b)
(file2 c)
```

We use predication of `file1` or `file2` to project out what we want.  
We will try this with an exec (the details of execs explored later).

`Basics_file1_file2_project.mm2`
```
; from `file1.mm2`
(file1 a)
(file1 b)

; from `file2.mm2`
(file2 b)
(file2 c)

(exec 0 
    (, (file1     $x) )
    (, (projected $x) )
)
```
run `./mork run Basics_file1_file2_project.mm2`

we get this.
```
(file1 a)
(file1 b)
(file2 b)
(file2 c)
(projected a)
(projected b)
```

`(file1 $x)` is a _prefix_ that lets us access the suffix set that will be bound to `$x`.

Predication will be used as an _indexing_ mechanism.
Data should (in general) be predicated to make querying only what one wants easier.

# Data
For the tutorial we will look at a rough overview of the data in MORK (see [Data in MORK]( https://github.com/trueagi-io/MORK/wiki/Data-in-MORK ) for a more details)

We have 3 primary ways to construct expressions
- Symbols `abc` | Numbers `1` | Strings `"a b c"`  
  (For the sake of this tutorial are equivalent)
- Tuples `( ... )`  
  All tuples have an associated arity (arity is the number of elements the tuple holds).
- Variables `$<VAR_NAME>`  
  Variables represent unbound values, having the same variable in an expression behaves as a reference (`($x $x)`);  
  when the value is bound, the reference will be bound to the same value; in a dual way it behaves as a constraint that both values must be the same.


# Basics of MM2

## Exec
MM2 looks like this 
```
(exec <priority> 
      <sources>
      <sinks>
)
```
When an exec is run, it is removed from the space.

## Priority
Where `<priority>` should be replaced with a ground s-expression.
The priority tells the runtime when an exec should be run relative to execs.

The order is based on path encoding of S-expressions; if you are curious see [Data in MORK]( https://github.com/trueagi-io/MORK/wiki/Data-in-MORK ).

The basic idea is that we can order priority like below :
- Low arity Tuple > High Arity Tuple > Short Symbol > Long Symbol

Have a look at the contents of the following files:
- `Basics_Priority_0_1.mm2`
- `Basics_Priority_0_(0_0).mm2`
- `Basics_Priority_(1)_(0 0).mm2`
- `Basics_Priority_(0_0)_(0_1).mm2`
- `Basics_Priority_1_00.mm2`
- `Basics_Priority_00_01.mm2`

Try to guess which exec will remain.

run them with `./mork run --steps 0 <FILE_NAME>`.

Compare your expectations with the outputs.

## Sources
Sources come in two variants,`(, ...)` and `(I ...)`.

The `,` list variant has patterns to match within MORK, successful matches create bindings for sinks.
Assume we wanted to match two patterns in the space, `(a $x)` and `(b $y)` we can construct this pattern list:
```
(, (a $x) (b $y) )
```
The `I` list variant adds more functionality and options.
Some include:
- `(ACT <filename> <pattern>)` : Matching from spaces on disk with the `.act` format
- `(== <pattern1> <pattern2>)` : Matching a pattern1 and a pattern2 bind if they unify.
- `(!= <pattern1> <pattern2>)` : Matching a pattern1 and a pattern2 bind if they don't unify.

This tutorial will be focusing solely on the `,` variant.

## Sinks
Sinks also come in two variants, `(, ...)` and `(O ...)`.


The `,` list variant has templates to write into MORK.

Say we had this space :
```
(a 1)
(a 2)
(b 3)
(exec 0
   (, (a $x) (b $y) )
   (, (ab $x $y)    )
)
```
run `./mork run Basics_Sources_Sinks.mm2`

When the exec is run the sources would generate these bindings: 
- `{ { $x => 1, $y => 3}, { $x => 2, $y => 3} }`

The template would be written out for all valid bindings:
- `(ab $x $y)[ { $x => 1, $y => 3} ]  => (ab 1 3)`
- `(ab $x $y)[ { $x => 2, $y => 3} ]  => (ab 2 3)`

The final space would look like this.
```
(a 1)
(a 2)
(b 3)
(ab 1 3)
(ab 2 3)
```

The `O` list variant adds more functionality and options.

Some include:
- `(+ <template>)` : equivalent to what `,` variant does.
- `(- <template>)` : removes the bound template from MORK and from all writes in the current transaction.

The `-` action is particularly useful, but use with care, it's behavior is non-monotonic.

```
(exec 0
    (, $x ) 
    (O 
        (- b)
    )
    
)

a
b
```
run `./mork run Basics_Sink_Removal.mm2`

it should output this
```
a
```

----

In `structuring_code_03_SetOps.md` we will look into how to make use of how to make simple transactions with exec, and unification.