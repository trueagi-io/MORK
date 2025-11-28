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
There are 2 points we are going to modify.

First is that there is no separation possible between two processes running execs this definition. Predication can make this possible.  
Second is that `eval` is hard coded in to join despite join being a rather general.

We still want the specialized version so we will need to stage creation of the `DEF`s.  
Define a `MACRO`, which signals (to ourselves) that it requires expansion.
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


Make an exec with a high priority (in our case higher than `(BEGIN-PROGRAM)`) that will expand our `MACROS`s to generate our `DEF`s.
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
(, (($fork_join $ctx) $val)           )
=>
(, (main eval ($fork_join $ctx) $val) )
```

run `./mork run Going_Wide_11_Macros.mm2`
We still get `(OUTPUT 1)`

Try running with `--steps 0`, `--steps 1`, ... and so on.
It's worthwhile to see how the program evolves.

----

Next we see if we can scale this program to more inputs in `structuring_code_05_Going_Wide_Macros.md`.
