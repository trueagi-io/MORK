# Going wide

_( This part of the tutorial is quite large, and it takes time to decompose the program. It could have been split up, but has been kept as a single section to signify that the various threads join up at the end of this section. )_

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
We are going to use these to evaluate the tree bottom up.
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
; 4 leaves got processed

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
It is important that the different values are on disjoint paths

This is better for pattern matching, we can now easily access the leaves and our path.
```
(($path <tag>) $leaf)
```
We can now look at what node a leaf is connected to.

For bare values:
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
( see  https://github.com/trueagi-io/MORK/wiki/Data-in-MORK )
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
run `./mork run --steps 0 Going_Wide_01_Recursive.mm2`

This exec unifies with itself ....
```
MGU : {
   $p0 => (, (exec 0 $p1 $t1) )
   $t0 => (, (exec 0 $p1 $t1) )
}
```
then templates itself.
```
(, (exec 0 $p0 $t0) )
=>
(, (exec 0 (, (exec 0 $p1 $t1) ) (, (exec 0 $p1 $t1) )) )
```
We get the same exec back.

The issue is that we want this to halt. We can do this by making it fail to match.  
We do so below by decrementing a counter (here with Peano arithmetic).
```
(counter (S (S (S Z))))
(exec LOOP (, (counter (S $N))
              (exec LOOP $p $t)
           )
           (O  (+ (exec LOOP $p $t)   ) 
               (+ (counter $N)     )
               (- (counter (S $N)) )
           )
)
```
run `./mork run --steps 0 Going_Wide_02_Halts.mm2`
you should find this
```
(counter (S (S Z)))
(exec LOOP (, (counter (S $a)) (exec LOOP $b $c)) (O (+ (exec 0 $b $c)) (+ (counter $a)) (- (counter (S $a)))))
```
the counter decremented by one Peano successor.

When the match fails at `(counter Z)`, the exec will be exhausted without making any writes, so it wont write itself back


We just need one more piece; we need to turn our INPUT in a form that is in the Path-Context representation.  
We will need to _fork_ our expressions in order to use our evaluation code to _join_ them.

Start with an empty path and our expression. Strip the top of the expression, make values when we find them, and fork more paths on recursive branches.

We need to distinguish between Our forks and our joins


Spawn a task to fork with our $INPUT
`DONE` here will help mark later that we have a finished computing.
```
((fork DONE) $INPUT)
```

Start with case/0; it simply converts it.
```
; case/0
(DEF fork
      (, ((fork $ctx) ($case/0)) )
      (, ((join ($ctx case/0)) $case/0) )
)
```
Then case/1 and case/2; Leave behind the case to join on and continue forking on the recursive part.
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

We can rewrite our joins to be in a similar form.
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
The `(RESET)` must have lower priority than `(TERM)`, and our forks and joins (it does).

let's run the full program.
run `./mork run Going_Wide_03.mm2`
Looking at the result we should find
```
(OUTPUT 1)
```

----

Next we generalize for and join with partial evaluation in `structuring_code_05_Going_Wide.md`.
