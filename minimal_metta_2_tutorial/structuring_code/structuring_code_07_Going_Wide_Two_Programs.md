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
Add to our `MACRO` expander :
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

Making these changes we are able to run our two programs at the same time.

run `./mork run Going_Wide_31_Two_Programs.mm2`

Look at the results, we can find :
```
(OUTPUT A 1)
(OUTPUT B 1)
(OUTPUT T ((node 4) ((node 6) ((node 7) (*) (*)) ((node 5) (*) (*))) ((node 2) ((node 3) (*) (*)) ((node 1) (*) (*)))))
```
The tree was successfully flipped. The other expressions evaluated.

----

Next we take stock in `structuring_code_In_Closing.md`.
