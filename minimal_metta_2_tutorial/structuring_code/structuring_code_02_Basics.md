# Basics

## Keeping Things Separate

(there is a PR for patterns and templates, but the bulk of the tutorial does not require patterns and templates for input and output to follow along, just for execs).

Say we have two metta files. 

"file_1.metta"
```
a
b
```
"file_2.metta"
```
b
c
```
and we import both with: 
- pattern  = `$x`
- template = `$x`

then export with the same pattern/template
we get:
```
a
b
c
```
So we can see that imports constitute a _set union_.

This may be the desired behavior, but often one would like to ensure that the separate files behave as separate sets.
This would require a form of _predication_.

We can do this simply by modifying the template on import.

Import "file1.metta" with
- pattern  = `$x`
- template = `(file1 $x)`

Import "file2.metta" with
- pattern  = `$x`
- template = `(file2 $x)`

Now we export with
- pattern  = `$x`
- template = `$x`
```
(file1 a)
(file1 b)
(file2 b)
(file2 c)
```
We still end up with a set union, but we can now use the predication of `file1` or `file2`
to project out what we want

export with
- pattern  = `(file1 $x)`
- template = `$x`
```
a
b
```

`(file $x)` is a _prefix_ that lets us access the suffix set that will be bound to `$x`.

In this tutorial we will only import one file at a time, so importing with a predication isn't needed, but the concept of predication is; predication will be used as an _indexing_ mechanism.
Data should (in general) be predicated to make querying only what one wants easier.

----

Consider the semantics of importing and exporting.
It basically follows a `read source -> write sink` paradigm.
This is transactional, it behaves as a single atomic action.
The read is filtered by the pattern while acquiring bindings, and templates shape the writes to the sink.
- Import is `read file -> write MORK`.
- Export is `read MORK -> write file`.

MM2 `exec`s introduce other interesting cases including:
- `read MORK -> write MORK`.

It actually goes much further, where you have multiple sources, and multiple sinks.

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

Some examples :
- `(0) > (1)`
- `(0) > (0 0)`
- `(1) > (0 0)`
- `(0 0) > (0 1)`
- `0 > 1`
- `1 > 00`
- `00 > 01`

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

----

In `structuring_code_03_SetOps.md` we will look into how to make use of how to make simple transactions with exec, and unification.