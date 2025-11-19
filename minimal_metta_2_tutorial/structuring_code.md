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

Let's think about the semantics of importing and exporting.
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
Functions in typical programming languages generally try to remove the concern of where values are. We will need to make that explicit.
The arguments locations, and the return locations are decided at the call site. Once the function is executed, the locations are know for the remainder of it's execution.

Lets work backward, we will assume we know where the locations are by using predication.
```
; we use `arg_a`, `arg_b` and `ret` as 'locations'
(exec 0
   (, (arg_a $val_a) 
      (arg_b $val_b)
   )
   (, (ret   $val_a) 
      (ret   $val_b) 
   )
)

; Here are some values at those 'locations'
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b d)
(arg_b e)
(arg_b f)
```

If we run our exec, we get this result.
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
; The definition is just data, 
;   the point is to find this data that has a useful shape dynamically.
((union ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $b)
    )
    (, ($out $a)
       ($out $b)
    )
)
; the argument data
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b d)
(arg_b e)
(arg_b f)

; what will search up our definition
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
unify : (1 2) x (1 2)        
MGU   : {}                                
subst : (1 2)
; constants match themselves

unify : $x (1 2)
MGU   : { $x => (1 2) }
subst : (1 2)
; free variables match any structure, structures match any free variable

unify : ($x 2) (1 $y) 
MGU   : { $x => 1, $y => 2 } 
subst : (1 2)
; matching happens on both sides

unify : (($x $y) (2 $y)) ((3 4) $z)
MGU   : { $x => 3, $y => 4, $z => (2 $y)}
subst : ((3 4) (2 4))
; shared variables share substitutions
```

We know have enough intuition to see how the union definition works.

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
Lets now substitute the exec's template
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

# The Set operations defined
We follow by defining each set operation.
Each one will have the same starting predicated sets, `(arg_a $elem_a)` and `(arg_b $elem_b)`
```
(arg_a a)
(arg_a b)
(arg_a c)
(arg_b b)
(arg_b c)
(arg_b d)
```

## Union
Union was explained above.
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
the exec using the definition
```
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
```
the exec using the definition
```
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
```
the exec using the definition
```
(exec 0 (, ((difference (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
after consuming the exec, it will leave behind these new values
```
(ret a)
```
## Symmetric difference
Symmetric difference could be implemented by computing the union, and the intersection, then taking the difference of the union and the intersection. The example below does this as a single transaction.
```
((symmetric-difference ($in_a $in_b) -> $out)
    (, ($in_a $a)
       ($in_b $b)
       ($in_a $mid)           
       ($in_b $mid)
    )
    (O (+ ($out $a)   )
       (+ ($out $b)   )
       (- ($out $mid) )
    )
)
```
the exec using the definition
```
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

MM2 code is better when it can process many expressions in a single transaction as possible. Sometimes this is easy and in general one should organize code such that it is so. Lets look at an example that requires splitting up.


Say one put this into the space for processing, and wanted to evaluate it.
```
(INPUT
   (if (or (1) 
           (not (and (or (1) (0))
                     (1)
                )
           )
       )
       (and (1) 
            (or (0) (1))
       )
   )
)
```
The goal is to compute an output `(OUTPUT $OUTPUT)`.

This expression is already an anti-pattern, but lets use this to ask:
"What expressions do I need to evaluate?" 
and
"Can I process many at once?"

Lets first describe what we have. We have booleans
```
; (ctor bool 1)
; (ctor bool 0)
```
We have boolean expression constructors
```
; (ctor bool-expr ($x))
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))
```
We now define a way to evaluate a bool-expr holding bools into a bool.

What follows are truth tables.
```
(eval (and 0 0) -> 0)
(eval (and 0 1) -> 0)
(eval (and 1 0) -> 0)
(eval (and 1 1) -> 1)

(eval (or 0 0) -> 0)
(eval (or 0 1) -> 1)
(eval (or 1 0) -> 1)
(eval (or 1 1) -> 1)

(eval (if 0 0) -> 1)
(eval (if 0 1) -> 1)
(eval (if 1 0) -> 0)
(eval (if 1 1) -> 1)

(eval (not 0) -> 1)
(eval (not 1) -> 0)

(eval (0) -> 0)
(eval (1) -> 1)
```
We are going to use these to compute the tree bottom up.
If we can expose any number of expressions in this shape, we can process them in bulk.

lets see how we would manually rewrite this using the above tables on a smaller example.
```
(and (or (1) (0))
     (if (1) (1))
)

=> (eval ($in) -> $out)
(and (or 1 0)
     (if 1 1)
)
; 4 leaves got processes

=> (eval ($bin_op $in_l $in_r) -> $out)
(and 1
     1
)
; 2 nodes got processed

=> (eval ($bin_op $in_l $in_r) -> $out)
1
; 1 node got processed
```
We could only apply the rules at what is effectively the current leaf of the tree we are collapsing.

The issue we face is that leaf values are not trivially pattern matched upon.

Let's think about why. Lets have a look at this expression again
```
(and (or (1) (0))
     (if (1) (1))
)
```
in order to match the leaves, we need to write a pattern that is at least as nested as the expression.
```
($op_0 ($op_1 ($l_00) ($l_01)) 
       ($op_2 ($l_10) ($l_11))
)
```

We are going to have to _invert_ this problem so that the value we match is trivial to access.

If the original expression was inverted, then the leaves would be at the top.
To describe this we will need multiple expressions
```
((.   case/2) and)
(((.  arg/1 ) case/2) or)
((((. arg/1 ) arg/1 ) case/0) 1)
((((. arg/1 ) arg/2 ) case/0) 0)
(((.  arg/2 ) case/2) if)
((((. arg/2 ) arg/1 ) case/0) 1)
((((. arg/2 ) arg/2 ) case/0) 1)
```
Other representations are possible, but it is important that the different values are on disjoint paths

This is better for pattern matching, we can now easily access the leaves.
```
(($path <tag>) $leaf)
```
We can now look at what node a leaf is connected too

for bare values
```
(, (($ctx case/0) $x)
   (eval ($x) -> $out)
)
```
for unary
```
(, (($ctx case/1) $op)
   (($ctx arg/1)  $x)
   (eval ($op $x) -> $out)
)
```
for binary
```
(, (($ctx case/2) $op)
   (($ctx arg/1)  $x)
   (($ctx arg/2)  $y)
   (eval ($op $x $y) -> $out)
)
```

Let's try an evaluation, in our case we will simply add our results in.
(values that no longer affect the computation will be shown together at the end)
```
((.   case/2) and)
(((.  arg/1)  case/2) or)
((((. arg/1)  arg/1 ) case/0) 1)
((((. arg/1)  arg/2 ) case/0) 0)
(((.  arg/2)  case/2) if)
((((. arg/2)  arg/1 ) case/0) 1)
((((. arg/2)  arg/2 ) case/0) 1)

=> (exec 0 (, (($ctx case/0) $x)
              (eval ($x) -> $out)
           )
           (, ($ctx $out) )
   )

((.   case/2) and)
(((.  arg/1)  case/2) or)
(((.  arg/1)  arg/1 ) 1)
(((.  arg/1)  arg/2 ) 0)
(((.  arg/2)  case/2) if)
(((.  arg/2)  arg/1 ) 1)
(((.  arg/2)  arg/2 ) 1)


=> (exec 0 (, (($ctx case/2) $op)
              (($ctx arg/1)  $x)
              (($ctx arg/2)  $y)
              (eval ($op $x $y) -> $out)
           )
           (, ($ctx $out) )
   )
((.   case/2) and)
((.   arg/1)  1)
((.   arg/2)  1)

=> (exec 0 (, (($ctx case/2) $op)
              (($ctx arg/1)  $x)
              (($ctx arg/2)  $y)
              (eval ($op $x $y) -> $out)
           )
           (, ($ctx $out) )
   )

; the final result
(. 1)


; the final space with only additions
(. 1)
((.   case/2) and)
((.   arg/1)  1)
((.   arg/2)  1)
(((.  arg/1)  case/2) or)
(((.  arg/1)  arg/1 ) 1)
(((.  arg/1)  arg/2 ) 0)
(((.  arg/2)  case/2) if)
(((.  arg/2)  arg/1 ) 1)
(((.  arg/2)  arg/2 ) 1)
((((. arg/1)  arg/1 ) case/0) 1)
((((. arg/1)  arg/2 ) case/0) 0)
((((. arg/2)  arg/1 ) case/0) 1)
((((. arg/2)  arg/2 ) case/0) 1)
```
This does what we set out to do, run multiple expressions at once.

This might look space inefficient, but it's less so than one might initially think, due to prefix compression.
```
[2] . 1
   [2] .   case/2 and
           arg/1  1
               2  1
      [2] .  arg/1  case/2 or
                 1  arg/1  1
                        2  0
                 2  case/2 if
                    arg/1  1
                        2  1
         [2]. arg/1  arg/1  case/0 1
                         2  case/0 0
                  2  arg/1  case/0 1
                         2  case/0 1
```
Still we will see later that using the `O` sink we can remove expressions that we will no longer need.

We now have a representation we can target, to exploit processing wide, layer by layer.
But to process layer by layer we are going to have to formulate our recursion (and ensure it terminates).

Making an infinite loop is not very hard, we just need the exec that keeps constructing itself
```
(exec 0 (, (exec 0 $p $t) )
        (, (exec 0 $p $t) )
)
```
This exec unifies with itself
```
MGU : {
   $p0 => (, (exec 0 $p1 $t1) )
   $t0 => (, (exec 0 $p1 $t1) )
}
```
Then templates itself
```
(, (exec 0 $p0 $t0) )
=>
(, (exec 0 (, (exec 0 $p1 $t1) ) (, (exec 0 $p1 $t1) )) )
```

The issue is that we want this to halt. We can do this either by making it fail to match.
We do so below by decrementing a counter.
```
(counter (S (S (S Z))))
(exec LOOP (, (counter (S $N))
              (exec LOOP $p $t) 
           )
           (O  (+ (exec 0 $p $t)   ) 
               (+ (counter $N)     )
               (- (counter (S $N)) )
           )
)
```
When the match fails at `(counter Z)`, the exec will be exhausted without making any writes, so it wont write itself back


We just need one more piece; we need to turn our INPUT in a form that is in the Path-Context representation.
We will need to _fork_ our expressions in order to use our evaluation code to _join_ them.

We will start with an empty path and our expression. We are going to strip the top of the expression, make values when we find them, and fork more paths on recursive branches.

We need to distinguish between Our forks and our joins


We'll spawn a task to fork with our $INPUT
`DONE` here will help mark later that we have a finished computing.
```
((fork DONE) $INPUT)
```

We start with case/0; it simply converts it.
```
; case/0
(DEF fork
      (, ((fork $ctx) ($case/0)) )
      (, ((join ($ctx case/0)) $case/0) )
)
```
then case/1 and case/2; We will leave behind the case to join on and continue forking on the recursive part.
```
; case/1
(DEF fork
      (, ((fork $ctx) ($case/1 $x))   )
      (, ((fork ($ctx arg/0 )) $x     )
         ((join ($ctx case/1)) $case/1)
      )
)
; case/2
(DEF fork
      (, ((fork $ctx) ($case/2 $x $y)))
      (, ((fork ($ctx arg/0 )) $x     )
         ((fork ($ctx arg/1 )) $y     )
         ((join ($ctx case/2)) $case/2)
      )
)
```

If the these are run in a loop an expression would be forked like so
```
((fork DONE) (and (or (1) (0))
                  (if (1) (1))
             )
) 
=> fork case/2
((join (DONE case/2)) and)
((fork (DONE arg/1)) (or (1) (0)))
((fork (DONE arg/2)) (if (1) (1)))

=> fork case/2
((join (DONE case/2)) and)
((join ((DONE arg/1 ) case/2)) or)
((fork ((DONE arg/1 ) arg/1 )) (1))
((fork ((DONE arg/1 ) arg/2 )) (0))
((join ((DONE arg/2 ) case/2)) if)
((fork ((DONE arg/2 ) arg/1 )) (1))
((fork ((DONE arg/2 ) arg/2 )) (1))

; we finally have all `join`
=>fork case/0
((join (DONE case/2)) and)
((join ((DONE arg/1) case/2)) or)
((join (((DONE arg/1) arg/1) case/0)) 1)
((join (((DONE arg/1) arg/2) case/0)) 0)
((join ((DONE arg/2) case/2)) if)
((join (((DONE arg/2) arg/1) case/0)) 1)
((join (((DONE arg/2) arg/2) case/0)) 1)
```

We can re write our joins to be in a similar form.
```
; case/0
(DEF join
      (, ((join ($ctx case/0)) $case/0)

         (eval ($case/0) -> $out)
      )
      (, ((join $ctx) $out) )
)
; case/1
(DEF join
      (, ((join ($ctx case/1)) $case/1)
         ((join ($ctx arg/0)) $x)

         (eval ($case/1 $x) -> $out)
      )
      (, ((join $ctx) $out)  )
)
; case/2
(DEF join
      (, ((join ($ctx case/2)) $case/2)
         ((join ($ctx arg/0 )) $x     )
         ((join ($ctx arg/1 )) $y     )

         (eval ($case/2 $x $y) -> $out)
      )
      (, ((join $ctx) $out)  )
)
```

We now have all our tools to make a main loop.
Before the main loop we need to initialize the process
```
(INPUT $INPUT) 
=>
((fork DONE) $INPUT)
```

Every time the main loop runs it will look for all our exec definitions, and itself.
```
(, (DEF fork $fork_p $fork_t)
   (DEF join $join_p $join_t)

   (exec MAIN $main-pattern $main-template)
)
```
It will spawn all the execs.
```
(exec (1 fork) $fork_p $fork_t)
(exec (0 join) $join_p $join_t)
```

Our termination condition is when we have our last join.
Once this runs it will write the output, then remove the process state.
```
(exec (TERM)
  (, ((join DONE) $OUTPUT)
     ((fork $f_env) $arg)
     ((join $j_env) $res)
  )
  (O (+ (OUTPUT $OUTPUT)   )
     (- ((fork $f_env) $arg) )
     (- ((join $j_env) $res) )
  )
)
```

When all the other execs have run, we reset the main loop when the conditions hold.
```
(exec (RESET)
  (, (($fork_join $ctx) $val)                 )
  (, (exec MAIN $main-pattern $main-template) )
)
```
the (RESET) must have lower priority than (TERM), and our forks and joins (it does).

Here is full program.
```
(eval (and 0 0) -> 0)
(eval (and 0 1) -> 0)
(eval (and 1 0) -> 0)
(eval (and 1 1) -> 1)

(eval (or 0 0) -> 0)
(eval (or 0 1) -> 1)
(eval (or 1 0) -> 1)
(eval (or 1 1) -> 1)

(eval (if 0 0) -> 1)
(eval (if 0 1) -> 1)
(eval (if 1 0) -> 0)
(eval (if 1 1) -> 1)

(eval (not 0) -> 1)
(eval (not 1) -> 0)

(eval (0) -> 0)
(eval (1) -> 1)

(INPUT
   (if (or (1)
           (not (and (or (1) (0))
                     (1)
                )
           )
       )
       (and (1) 
            (or (0) (1))
       )
   )
)

; case/0
(DEF fork
      (, ((fork $ctx) ($case/0)) )
      (, ((join ($ctx case/0)) $case/0) )
)
; case/1
(DEF fork
      (, ((fork $ctx) ($case/1 $x))   )
      (, ((fork ($ctx arg/0 )) $x     )
         ((join ($ctx case/1)) $case/1)
      )
)
; case/2
(DEF fork
      (, ((fork $ctx) ($case/2 $x $y)))
      (, ((fork ($ctx arg/0 )) $x     )
         ((fork ($ctx arg/1 )) $y     )
         ((join ($ctx case/2)) $case/2)
      )
)


; case/0
(DEF join
      (, ((join ($ctx case/0)) $case/0)

         (eval ($case/0) -> $out)
      )
      (, ((join $ctx) $out) )
)
; case/1
(DEF join
      (, ((join ($ctx case/1)) $case/1)
         ((join ($ctx arg/0)) $x)

         (eval ($case/1 $x) -> $out)
      )
      (, ((join $ctx) $out)  )
)
; case/2
(DEF join
      (, ((join ($ctx case/2)) $case/2)
         ((join ($ctx arg/0 )) $x     )
         ((join ($ctx arg/1 )) $y     )

         (eval ($case/2 $x $y) -> $out)
      )
      (, ((join $ctx) $out)  )
)

(exec (BEGIN-PROGRAM) 
  (, (INPUT $INPUT) 
  )
  (,
    ((fork DONE) $INPUT)

    (exec MAIN 
      (, 
         (DEF fork $fork_p $fork_t)
         (DEF join $join_p $join_t)

         (exec MAIN $main-pattern $main-template)
      )
      (, 
         (exec (1 fork) $fork_p $fork_t)
         (exec (0 join) $join_p $join_t)

         (exec (TERM)
           (, ((join DONE) $OUTPUT)
              ((fork $f_env) $arg)
              ((join $j_env) $res)
           )
           (O (+ (OUTPUT $OUTPUT)   )
              (- ((fork $f_env) $arg) )
              (- ((join $j_env) $res) )
           )
         )

         (exec (RESET)
           (, (($fork_join $ctx) $val)                 )
           (, (exec MAIN $main-pattern $main-template) )
         )
      )
    )
  )
)
```


# Macros as staged partial evaluation

Sometimes it can be helpful to keep a definition generic, but specialize it before doing future processing.

Lets have a look at some of the `DEF`s.
```
; case/2
(DEF join
      (, ((join ($ctx case/2)) $case/2)
         ((join ($ctx arg/0 )) $x     )
         ((join ($ctx arg/1 )) $y     )

         (eval ($case/2 $x $y) -> $out)
      )
      (, ((join $ctx) $out)  )
)
```
There are currently 2 points we are going to modify.
First is that there is no separation possible between two processes running execs this definition.
Predication can make this possible.
Second is that `eval` is hard coded in to join despite join being a rather general.

We still want the specialized version so we will need to stage creation of the `DEF`s.
We'll define a `MACRO`, which just signals it requires a moment of staging.
```
; case/2
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/2)) $case/2)
         ($proc $op (join ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx arg/1 )) $y     )

         ($op ($case/2 $x $y) -> $out)
      )
      (, ($proc $op (join $ctx) $out)
      )
)
```
- `$proc` predicates the values to a namespace.
- `$op` will select what operation we will be running (in our case`$op`).


We then make an exec with a high priority (in our case higher than `(BEGIN-PROGRAM)`) that will expand our `MACROS`s to generate our `DEF`s.
```
; the macro creates DEF, the MACROS are \"compiled out\"
(exec (macro) 
  (,
     (MACRO ($name main eval) $p $t)
  )
  (, (DEF   ($name main eval) $p $t)
  )
)
```

The main loop is then modified to use the modified `DEF`s.
```
; the `MAIN` sources
(, 
   (DEF fork $fork_p $fork_t)
   (DEF join $join_p $join_t)

   (exec MAIN $main-pattern $main-template)
)
=>
(, 
   (DEF (fork main eval) $fork_p $fork_t)
   (DEF (join main eval) $join_p $join_t)
   
   (exec MAIN $main-pattern $main-template)
)


; The `(TERM)` sources
(, ((join DONE) $OUTPUT)
   ((fork $f_env) $arg)
   ((join $j_env) $res)
)
=>
(, (main eval (join DONE) $OUTPUT)
   (main eval $env $arg)
)


; The `(TERM)` sinks
(O (+ (OUTPUT $OUTPUT)   )
   (- ((fork $f_env) $arg) )
   (- ((join $j_env) $res) )
)
=>
(O (+ (OUTPUT $OUTPUT)      )
   (- (main eval $env $arg) )
)

; The (RESET) exec sources
(, (($fork_join $ctx) $val)                 )
=>
(, (main eval ($fork_join $ctx) $val)       )
```

The modified code in total looks like this
```
(eval (and 0 0) -> 0)
(eval (and 0 1) -> 0)
(eval (and 1 0) -> 0)
(eval (and 1 1) -> 1)

(eval (or 0 0) -> 0)
(eval (or 0 1) -> 1)
(eval (or 1 0) -> 1)
(eval (or 1 1) -> 1)

(eval (if 0 0) -> 1)
(eval (if 0 1) -> 1)
(eval (if 1 0) -> 0)
(eval (if 1 1) -> 1)

(eval (not 0) -> 1)
(eval (not 1) -> 0)

(eval (0) -> 0)
(eval (1) -> 1)


(INPUT
   (if (or (1) 
           (not (and (or (1) (0))
                     (1)
                )
           )
       )
       (and (1) 
            (or (0) (1))
       )
   )
)

; case/0 
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/0)) )
      (, ($proc $op (join ($ctx case/0)) $case/0) )
)
; case/1
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/1 $x))
      )
      (, ($proc $op (fork ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx case/1)) $case/1)
      )
)
; case/2
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/2 $x $y))

      )
      (, ($proc $op (fork ($ctx arg/0 )) $x     )
         ($proc $op (fork ($ctx arg/1 )) $y     )
         ($proc $op (join ($ctx case/2)) $case/2)
      )
)


; case/0
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/0)) $case/0)

         ($op ($case/0) -> $out)
      )
      (, ($proc $op (join $ctx) $out) 
      )
)
; case/1
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/1)) $case/1)
         ($proc $op (join ($ctx arg/0)) $x)
         
         ($op ($case/1 $x) -> $out)
      )
      (, ($proc $op (join $ctx) $out)
      )
)
; case/2
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/2)) $case/2)
         ($proc $op (join ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx arg/1 )) $y     )

         ($op ($case/2 $x $y) -> $out)
      )
      (, ($proc $op (join $ctx) $out)
      )
)



; the macro creates DEF, the MACROS are \"compiled out\"
(exec (macro) 
  (,
     (MACRO ($name main eval) $p $t)
  )
  (, (DEF   ($name main eval) $p $t)
  )
)

; this should fire right when macros are done expanding
(exec (BEGIN-PROGRAM) 
  (, (INPUT $INPUT)
  )
  (,
    (main eval (fork DONE) $INPUT)

    (exec MAIN 
      (, 
         (DEF (fork main eval) $fork_p $fork_t)
         (DEF (join main eval) $join_p $join_t)
         
         (exec MAIN $main-pattern $main-template)
      )  
      (, 
         (exec (1 fork) $fork_p $fork_t)
         (exec (0 join) $join_p $join_t)
         
         (exec (TERM)
           (, (main eval (join DONE) $OUTPUT)
              (main eval $env $arg)
           )
           (O (+ (OUTPUT $OUTPUT)      )
              (- (main eval $env $arg) )
           )
         )

         (exec (RESET)
           (, (main eval ($fork_join $ctx) $val)       )
           (, (exec MAIN $main-pattern $main-template) )
         )
      )
    )
  )
)
```

# Running larger programs
At the moment only one input expression is being processed at a time.


Say the `(INPUT $expression)` was modified with a tag like this `(INPUT $tag $expression)`.
Then one could query the outputs based on tag with `(OUTPUT $tag $result)`.

The modification to the `MAIN` loop is minor, the main difference is that we will modify the `DONE` in the evaluation context to hold the tag: `(DONE $TAG)`.

This will work (the modified code shown later).

Let's now consider that currently we only clear temporary expressions once an evaluation terminates.

On smaller expressions this is fine, but as expressions grow, and the number of input grows the memory we use could become a limitation.

In our program there are clear points that we know an expression will not be needed anymore. We could remove those expressions using a `(O (- ...` sink.
(It should be noted that using a `,` sink is often a fast-path, but we are optimizing now for space).

lets look at the `(MACRO (fork ....` code for an example.
```
; case/1
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/1 $x))
      )
      (, ($proc $op (fork ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx case/1)) $case/1)
      )
)
```

After the fork happens, we don't need to spawn it again, so we could remove it. We modify it like so:
```
; case/2
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/2 $x $y))

      )
      (O 
         (+ ($proc $op (fork ($ctx arg/0)) $x     ) )
         (+ ($proc $op (fork ($ctx arg/1)) $y     ) )
         (+ ($proc $op (join ($ctx case/2)) $case/2) )


         (- ($proc $op (fork $ctx) ($case/2 $x $y)) )
      )
)
```
Note how we remove what we matched `($proc $op (fork $ctx) ($case/2 $x $y))`.

In some sense we can see this pattern as an expression going out of scope.

We can see that join can be modified similarly:
```
; case/2
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/2)) $case/2)
         ($proc $op (join ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx arg/1 )) $y     )

         ($op ($case/2 $x $y) -> $out)
      )
      (O (+ ($proc $op (join $ctx) $out) )

         (- ($proc $op (join ($ctx case/2)) $case/2) )
         (- ($proc $op (join ($ctx arg/0 )) $x     ) )
         (- ($proc $op (join ($ctx arg/1 )) $y     ) )
      )
)
```
This looks more involved, but this is only because the 3 expressions we join all go out of scope together.
It can be helpful to visually "brace" the scope by putting the value that will go out of scope at the top and bottom of the exec, with the rest of the transaction in the middle.

After putting all this together the code looks like this:
```
(eval (and 0 0) -> 0)
(eval (and 0 1) -> 0)
(eval (and 1 0) -> 0)
(eval (and 1 1) -> 1)

(eval (or 0 0) -> 0)
(eval (or 0 1) -> 1)
(eval (or 1 0) -> 1)
(eval (or 1 1) -> 1)

(eval (if 0 0) -> 1)
(eval (if 0 1) -> 1)
(eval (if 1 0) -> 0)
(eval (if 1 1) -> 1)

(eval (not 0) -> 1)
(eval (not 1) -> 0)

(eval (0) -> 0)
(eval (1) -> 1)

(INPUT A
   (if (or (1) 
           (not (and (or (1) (0))
                     (1)
                )
           )
       )
       (and (1) 
            (or (0) (1))
       )
   )
)
(INPUT B
   (if (and (1) 
            (or (0) (1))
       )
       (or (1) 
           (not (and (or (1) (0))
                     (1)
                )
           )
       )
   )
)

; case/0 
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/0))

      )
      (O
        (+ ($proc $op (join ($ctx case/0)) $case/0) )


        (- ($proc $op (fork $ctx) ($case/0)) )
      )
)
; case/1
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/1 $x))
      
      )
      (O 
         (+ ($proc $op (fork ($ctx arg/0)) $x)      )
         (+ ($proc $op (join ($ctx case/1)) $case/1) )

         (- ($proc $op (fork $ctx) ($case/1 $x)) )
      )
)
; case/2
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/2 $x $y))

      )
      (O 
         (+ ($proc $op (fork ($ctx arg/0)) $x     ) )
         (+ ($proc $op (fork ($ctx arg/1)) $y     ) )
         (+ ($proc $op (join ($ctx case/2)) $case/2) )


         (- ($proc $op (fork $ctx) ($case/2 $x $y)) )
      )
)


; case/0
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/0)) $case/0)

         ($op ($case/0) -> $out)
      )
      (O 
         (+ ($proc $op (join $ctx) $out) )

         (- ($proc $op (join ($ctx case/0)) $case/0) )
      )
)
; case/1
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/1)) $case/1)
         ($proc $op (join ($ctx arg/0)) $x)
         
         ($op ($case/1 $x) -> $out)
      )
      (O (+ ($proc $op (join $ctx) $out) )

         (- ($proc $op (join ($ctx case/1)) $case/1) )
         (- ($proc $op (join ($ctx arg/0 )) $x     ) )
      )
)
; case/2
(MACRO
  (join $proc $op)
      (, ($proc $op (join ($ctx case/2)) $case/2)
         ($proc $op (join ($ctx arg/0 )) $x     )
         ($proc $op (join ($ctx arg/1 )) $y     )

         ($op ($case/2 $x $y) -> $out)
      )
      (O (+ ($proc $op (join $ctx) $out) )

         (- ($proc $op (join ($ctx case/2)) $case/2) )
         (- ($proc $op (join ($ctx arg/0 )) $x     ) )
         (- ($proc $op (join ($ctx arg/1 )) $y     ) )
      )
)



; the macro creates DEF, the MACROS are \"compiled out\"
(exec (macro) 
  (,
     (MACRO ($name main eval) $p $t)
     (MACRO ($name $proc $op) $pattern $template)
  )
  (O 
     (+ (DEF   ($name main eval) $p $t) )

     (- (MACRO ($name $proc $op) $pattern $template) )
  )
)

; this should fire right when macros are done expanding
(exec (BEGIN-PROGRAM) 
  (, (INPUT $TAG $INPUT)
  )
  (,
    (main eval (fork (DONE $TAG)) $INPUT)

    (exec MAIN 
      (, 
         (DEF (fork main eval) $fork_p $fork_t)
         (DEF (join main eval) $join_p $join_t)
         
         (exec MAIN $main-pattern $main-template)
      ) 
      (, 
         (exec (1 fork) $fork_p $fork_t) 
         (exec (0 join) $join_p $join_t) 
         
         (exec (TERM)
           (, (main eval (join (DONE $TAG_)) $OUTPUT)
           )
           (O (+ (OUTPUT $TAG_ $OUTPUT) )

              (- (main eval (join (DONE $TAG_)) $OUTPUT) )
           )
         )

         (exec (RESET)
           (, (main eval ($fork_join $ctx) $val)       )
           (, (exec MAIN $main-pattern $main-template) )
         )
      )
    )
  )
)
```

# Running multiple programs

Let's add another program into the mix.
The program will take a binary tree and flip it.
We will reuse the logic of our fork join.
To do so we need to only have recursive parts at the fork points.
Non-recursive parts need to be held in the head of the nodes
```

; (ctor tree (*))
; (ctor tree ((node $n) $x $y))

(flip-tree ((node $val) $x $y) -> ((node $val) $y $x))
(flip-tree (*) -> (*))

; if it was infix
(INPUT-TREE T 
   ((node 4)
      ((node 2) 
         ((node 1) (*) (*))
         ((node 3) (*) (*))
      )
      ((node 6)
         ((node 5) (*) (*))
         ((node 7) (*) (*))
      )
   )
)
```
We'll add to our `MACRO` expander
```
(exec (macro) 
  (,
     (MACRO ($name $proc $op) $pattern $template)

     (MACRO ($name main eval) $p $t)
     (MACRO ($name main flip-tree) $p_ $t_)
  )
  (O 
     (+ (DEF   ($name main eval)      $p $t) )
     (+ (DEF   ($name main flip-tree) $p_ $t_) )

     (- (MACRO ($name $proc $op) $pattern $template) )
  )
)
```

And modify `(BEGIN-PROGRAM)` to spawn the `INPUT-TREE`.
We generalize the body from eval to `$op` and `$op_`.
```
(exec (BEGIN-PROGRAM) 
  (, (INPUT $TAG $INPUT)
     (INPUT-TREE $TAG-TREE $INPUT-TREE)
  )
  (,
    (main eval      (fork (DONE $TAG     )) $INPUT     )
    (main flip-tree (fork (DONE $TAG-TREE)) $INPUT-TREE)

    (exec MAIN 
      (, 
         (DEF (fork main $op) $fork_p $fork_t)
         (DEF (join main $op) $join_p $join_t)
         
         (exec MAIN $main-pattern $main-template)
      ) 
      (, 
         (exec (1 fork) $fork_p $fork_t) 
         (exec (0 join) $join_p $join_t) 
         
         (exec (TERM)
           (, (main $op_ (join (DONE $TAG_)) $OUTPUT)
           )
           (O (+ (OUTPUT $TAG_ $OUTPUT) )

              (- (main $op_ (join (DONE $TAG_)) $OUTPUT) )
           )
         )

         (exec (RESET)
           (, (main $op ($fork_join $ctx) $val)       )
           (, (exec MAIN $main-pattern $main-template) )
         )
      )
    )
  )
)
```