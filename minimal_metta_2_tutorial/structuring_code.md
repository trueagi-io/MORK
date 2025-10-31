Structuring a program in MM2 can be a little daunting.



say we have a simple set of finite functions
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

; (ctor bool (1))
; (ctor bool (0))
; (ctor bool (and $x $y))
; (ctor bool (or  $x $y))
; (ctor bool (xor $x $y))
; (ctor bool (if  $x $y))

(INPUT 
   (if (or (1) 
           (and (or (1) (0))
                (1)
           )
       )
       (and (1) 
            (or (0) (1))
       )
   )
)



```

# Fork Join

eval
```
; case/0 
(MACRO
  (fork $proc $op)
      (, ($proc $op (fork $ctx) ($case/0))

      )
      (O
        (+ ($proc $op (join $ctx) $case/0) )


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
      (, ($proc $op (join $ctx) ($case/0))

         ($op ($case/0) -> $out)
      )
      (O 
         (+ ($proc $op (join $ctx) $out) )

         (- ($proc $op (join $op $ctx) ($case/0)) )
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

```

# Entry Point
```

; the macro creates defs
(exec (macro) 
  (,
     (MACRO ($name main eval) $p $t)
     (MACRO ($name $proc $op) $pattern $template)
  )
  (O 
     (+ (DEF   ($name main eval) $p $t) )
     (+ MACROS_EXPANDED                 )

     (- (MACRO ($name main eval) $p $t)              )
     (- (MACRO ($name $proc $op) $pattern $template) )
  )
)

; this should fire right when macros are done expanding
(exec (BEGIN-PROGRAM) 
  (, MACROS_EXPANDED
     (INPUT $N $INPUT)
  )
  (,
    (main eval (fork (DONE $N)) $INPUT)

    (exec MAIN 
      (, 
         (DEF (fork main eval) $fork_p $fork_t)
         (DEF (join main eval) $join_p $join_t)
         
         (exec MAIN $main-pattern $main-template)
      ) 
      (, 
         (exec (1 fork) $fork_p $fork_t) 
         (exec (0 join) $join_p $join_t) 
         
         (exec MAIN $main-pattern $main-template)

         (exec (TERM)
           (, (main eval (join (DONE $N_)) $OUTPUT)
              (exec MAIN $patterns $templates)
           
           )
           (O (+ (OUTPUT $N_ $OUTPUT) )

              (- (main eval (join (DONE $N_)) $OUTPUT) )
           )
         )
      )
    )
  )
)


```
