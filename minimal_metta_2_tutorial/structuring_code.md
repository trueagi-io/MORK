Structuring a program in MM2 can be a little daunting.





Let start with some basics.

# Keeping Things Separate

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
So we can see that imports constitute a set union.

This may be the desired behavior, but often one would like to ensure that the separate files behave as separate sets.
This would require a form of _predication_.

We can do this simply by modifying the template on import.

import "file1.metta" with
- pattern  = `$x`
- template = `(file1 $x)`


import "file2.metta" with
- pattern  = `$x`
- template = `(file2 $x)`

now if we export with
- pattern  = `$x`
- template = `$x`
```
(file1 a)
(file1 b)
(file2 b)
(file2 c)
```
We still end up with a set union, but we can now use the predication
to project out what we want

export with
- pattern  = `(file1 $x)`
- template = `$x`
```
a
b
```

`(file $x)` is _prefix_ that lets us access the suffix set that will be bound to `$x`.

Lets think about the semantics of importing and exporting.
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

The order is based on path encoding of S-expressions ( if you are curious https://github.com/trueagi-io/MORK/wiki/Data-in-MORK ).

The basic idea is that we can order priority like below

Low arity Tuple > High Arity Tuple > Short Symbol > Long Symbol

some examples
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

The earlier pattern list could be done more verbosely as:
```
(I (== (a $x) $ax) (== (b $y) $by) )
```

This tutorial will mostly be focusing on the `,` variant.


## Sinks
Sinks also come in two variants, `(, ...)` and `(O ...)`.


The `,` list variant has templates to write into MORK.
Say we had this space
```
(a 1)
(a 2)
(b 3)
(exec 0
   (, (a $x) (b $y) )
   (, (ab $x $y)    )
)
```
When the exec is run
The sources would generate these bindings: `{ { $x => 1, $y => 3}, { $x => 2, $y => 3} }`.
the template would be written out for all valid bindings:
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

The `-` action is particularly useful, but know that often it is better to create a new predicated set, than to remove from an existing set. Use with care, it's behavior is non-monotonic.

# Basic Set Operations

In set theory there are basic operations like union, intersection, difference and symmetric difference.

These can done naturally, if we remember that we need to predicate our sets in order to keep them distinct.

Lets look at what union as a function looks like and work from there.
```
union : Set x Set -> Set
```
Functions generally try to remove the concern of where values are. We will need to make that explicit.
The arguments locations, and the return locations are decided at the call site. Once the function is executed, the locations are know for the remainder of it's execution.

Lets work backward, we will assume we know where the locations are by using predication.
```
; we use arg_a, arg_b and ret as 'locations'
(exec 0
   (, (arg_a $val_a) 
      (arg_b $val_b)
   )
   (, (ret   $val_a) 
      (ret   $val_b) 
   )
)

; lets have some concrete locations to boot
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b d)
(arg_b e)
(arg_b f)
```

if we run our exec, we get this result
```
(ret a)
(ret b)
(ret c)
(ret d)
(ret e)
(ret f)
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b d)
(arg_b e)
(arg_b f)
```
not bad!

So how do we avoid hard coding our locations, and make this reusable?

We need an exec to build an exec!
Our first exec will need a union definition:
```
; the definition
((union ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $b)
    )
    (, ($out $a)
       ($out $b)
    )
)
; the data
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b d)
(arg_b e)
(arg_b f)

(exec 0 (, ((union (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
This works!
Let's break down why.
The main workhorse here is unification.

## Unification
Unification is a form of bidirectional pattern matching.

Unification either fails to match, or succeeds to find the "Most General Unifier", the MGU.
The MGU is a substitution set that if applied to either argument will
result in the same value.

Lets just examine some example arguments and results
```
(1 2)           (1 2)        MGU{}                                | (1 2)
; constants match themselves

$x              (1 2)        MGU{ $x => (1 2) }                   | (1 2)
; free variables match any structure, structures match any free variable

($x 2)          (1 $y)       MGU{ $x => 1, $y => 2 }              | (1 2)
; matching happens on both sides

(($x $y) (2 $y)) ((3 4) $z)  MGU{ $x => 3, $y => 4, $z => (2 $y)} | ((3 4) (2 4))
; shared variables share substitutions
```

We know have enough intuition to see how the union definition.
The exec has this pattern:
```
((union (arg_a arg_b) -> ret) $p $t)
```
The definition is here:
```
((union ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $b)
    )
    (, ($out $a)
       ($out $b)
    )
)
```
Here is the MGU:
```
MGU
{ $in_a => arg_a
, $in_b => arg_b
, $out  => ret
, $p    => (, ($in_a $a)           
              ($in_b $b)
           )
, $t    => (, ($out $a)
              ($out $b)
           )
}
```
We can then apply the MGU to itself until it has no more recursive parts.
(In this case look at the $in_a $in_b and $out in $p and $t)
```
MGU
{ $in_a => arg_a
, $in_b => arg_b
, $out  => ret
, $p    => (, (arg_a $a)           
              (arg_b $b)
           )
, $t    => (, (ret $a)
              (ret $b)
           )
}
```
We see what $p and $t are now.
Lets now substitute the exec's template itself
```
; substitute $p and $t
(exec 0 $p $t)

; becomes what we wrote originally!
(exec 0
   (, (arg_a $a)           
      (arg_b $b)
   )
   (, (ret $a)
      (ret $b)
   )
)
```

Take time to really understand this!
We looked up a "specialized" version of an expression by unifying it's variables with constants.
The shared parts we unified with broadcasted those constants to the other parts of the expression.

## Union
We explained it above the following just puts it in the format of the other operations to show.
```
((union ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $b)
    )
    (, ($out $a)
       ($out $b)
    )
)

(arg_a a)
(arg_a b)
(arg_a c)
(arg_b b)
(arg_b c)
(arg_b d)

(exec 0 (, ((union (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
After consuming the exec, it will leave behind these new values.
```
(ret a)
(ret b)
(ret c)
(ret d)
```

## Intersection

For intersection we need to have the __constraint__ that both argument elements are the same value
```
((intersection ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $a)
    )
    (, ($out $a) )
)

(arg_a a)
(arg_a b)
(arg_a c)
(arg_b b)
(arg_b c)
(arg_b d)

(exec 0 (, ((intersection (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
after consuming the exec, it will leave behind these new values
```
(ret b)
(ret c)
```

## Difference
Set difference we need to just make sure the order of the arguments are clear. 
The right argument will remove from the left. We are going to need to use the `O` sink.
```
((difference ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $b)
    )
    (O (+ ($out $a) )
       (- ($out $b) )
    )
)

(arg_a a)
(arg_a b)
(arg_a c)
(arg_b b)
(arg_b c)
(arg_b d)

(exec 0 (, ((difference (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
after consuming the exec, it will leave behind these new values
```
(ret a)
```
## Symmetric difference
```
((symmetric-difference ($in_a $in_b) -> $out)
    (, ($in_a $a)
       ($in_a $mid)           
       ($in_b $mid)
       ($in_b $b)
    )
    (O (+ ($out $a)   )
       (+ ($out $b)   )
       (- ($out $mid) )
    )
)
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b b)
(arg_b c)
(arg_b d)

(exec 0 (, ((symmetric-difference (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
after consuming the exec, it will leave behind these new values
```
(ret a)
(ret d)
```

# Closing on Set operations

Generally these operations need not be defined, rather they should be understood.
Set operations are effectively implicitly happening every time you make make a query.
More sophisticated actions are usually subtle variations of these examples above, with more domain specific behavior.

# Going wide

MM2 code is better when it can process many simultaneously.

































