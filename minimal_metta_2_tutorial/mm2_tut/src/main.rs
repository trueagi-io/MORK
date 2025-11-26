
#[inline]fn id<T>(t:T)->T {t}

mod data;
mod relational_algebra;

pub(crate) mod boolean_alg {

    use std::io::{Write};

mod boolean_alg_archive {

const BOOLEAN_ALG : &str ="

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

; (ctor bool 1)
; (ctor bool 0)
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))

(INPUT 0
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

; (INPUT 1
;    (if (or (1) 
;            (and (or (1) (0))
;                 (if (or (1) 
;                         (and (or (1) (0))
;                              (1)
;                         )
;                     )
;                     (and (1) 
;                          (or (0) (1))
;                     )
;                 )
;            )
;        )
;        (and (1) 
;             (or (0) (1))
;        )
;    )
; )

; (INPUT 2
;    (if (or (1) 
;            (and (or (1) (0))
;                 (if (or (1) 
;                         (and (or (1) (0))
;                              (1)
;                         )
;                     )
;                     (and (if (or (1) 
;                                  (and (or (1) (0))
;                                       (if (or (1) 
;                                               (and (or (1) (0))
;                                                    (1)
;                                               )
;                                           )
;                                           (and (1) 
;                                                (or (0) (1))
;                                           )
;                                       )
;                                  )
;                              )
;                              (and (1) 
;                                   (or (0) (1))
;                              )
;                          )
;                          (or (0) (1))
;                     )
;                 )
;            )
;        )
;        (and (1) 
;             (or (0) (1))
;        )
;    )
; )

 (INPUT 3
   (and
     (or
       (if
        (and
          (and
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
          (and
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
        (or
          (if
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
          )
          (and
            (and
              (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
                (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
                (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
      )
       (and
        (and
          (or
            (if
              (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
                (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
            )
            (if
              (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
                (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
            )
          )
          (if
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
          )
        )
        (and
          (and
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
          (and
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
       )
     )
     (or
       (if
        (and
          (and
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
          (and
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
        (or
          (if
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
          )
          (and
            (and
              (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
                (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
                (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
      )
       (and
        (and
          (or
            (if
              (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
                (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
            )
            (if
              (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
                (and
                ( or( if(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     ( or(1) (1))
                )
              )
            )
          )
          (if
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
            (and
              (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
                (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
            )
          )
        )
        (and
          (and
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (and
              (or
                ( if(and (1) (1))
                     (and (1) (1))
                )
                (and ( or(1) (1))
                     ( if(1) (1))
                )
              )
                (and
                (and (and (1) (1))
                     ( or(1) (1))
                )
                ( if(and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
          (and
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     ( if(1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
            (or
              (if
                (and (and (1) (1))
                     (and (1) (1))
                )
                ( or( if(1) (1))
                     (and (1) (1))
                )
              )
                (and
                (and ( or(1) (1))
                     (and (1) (1))
                )
                (and (and (1) (1))
                     (and (1) (1))
                )
              )
            )
          )
        )
       )
     )
   )
 )

; (INPUT_ 4
;    (if (or (1) 
;            (and (or (1) (0))
;                 (if (or (1) 
;                         (and (or (1) (0))
;                              (1)
;                         )
;                     )
;                     (and (if (or (1) 
;                                  (and (or (1) (0))
;                                       (if (or (1) 
;                                               (and (or (1) (0))
;                                                    (1)
;                                               )
;                                           )
;                                           (and (1) 
;                                                (or (0) (1))
;                                           )
;                                       )
;                                  )
;                              )
;                              (and (1) 
;                                   (or (0) (1))
;                              )
;                          )
;                          (or (0) 
;                              (if (or (1) 
;                                      (and (or (1) (0))
;                                           (if (or (1) 
;                                                   (and (or (1) (0))
;                                                        
;                                                        (if (or (1) 
;                                                                (and (or (1) (0))
;                                                                     (if (or (1) 
;                                                                             (and (or (1) (0))
;                                                                                  (1)
;                                                                             )
;                                                                         )
;                                                                         (and (if (or (1) 
;                                                                                      (and (or (1) (0))
;                                                                                           (if (or (1) 
;                                                                                                   (and (or (1) (0))
;                                                                                                        (1)
;                                                                                                   )
;                                                                                               )
;                                                                                               (and (1) 
;                                                                                                    (or (0) (1))
;                                                                                               )
;                                                                                           )
;                                                                                      )
;                                                                                  )
;                                                                                  (and (1) 
;                                                                                       (or (0) (1))
;                                                                                  )
;                                                                              )
;                                                                              (or (0) 
;                                                                                  (if (or (1) 
;                                                                                          (and (or (1) (0))
;                                                                                               (if (or (1) 
;                                                                                                       (and (or (1) (0))
;                                                                                                            (1)
;                                                                                                       )
;                                                                                                   )
;                                                                                                   (and (if (or (1) 
;                                                                                                                (and (or (1) (0))
;                                                                                                                     (if (or (1) 
;                                                                                                                             (and (or (1) (0))
;                                                                                                                                  (1)
;                                                                                                                             )
;                                                                                                                         )
;                                                                                                                         (and (1) 
;                                                                                                                              (or (0) (1))
;                                                                                                                         )
;                                                                                                                     )
;                                                                                                                )
;                                                                                                            )
;                                                                                                            (and (1) 
;                                                                                                                 (or (0) (1))
;                                                                                                            )
;                                                                                                        )
;                                                                                                        (or (0) (1))
;                                                                                                   )
;                                                                                               )
;                                                                                          )
;                                                                                      )
;                                                                                      (and (1) 
;                                                                                           (or (0) (1))
;                                                                                      )
;                                                                                  )
;                                                                              )
;                                                                         )
;                                                                     )
;                                                                )
;                                                            )
;                                                            (and (1) 
;                                                                 (or (0) (1))
;                                                            )
;                                                        )
;                                                   )
;                                               )
;                                               (and (if (or (1) 
;                                                            (and (or (1) (0))
;                                                                 (if (or (1) 
;                                                                         (and (or (1) (0))
;                                                                              (1)
;                                                                         )
;                                                                     )
;                                                                     (and (1) 
;                                                                          (or (0) (1))
;                                                                     )
;                                                                 )
;                                                            )
;                                                        )
;                                                        (and (1) 
;                                                             (or (0) (1))
;                                                        )
;                                                    )
;                                                    (or (0) (1))
;                                               )
;                                           )
;                                      )
;                                  )
;                                  (and (1) 
;                                       (or (0) (1))
;                                  )
;                              )
;                          )
;                     )
;                 )
;            )
;        )
;        (and (1) 
;             (or (0) (1))
;        )
;    )
; )


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

     (- (MACRO ($name main eval) $p $t)              )
     (- (MACRO ($name $proc $op) $pattern $template) )
  )
)

; this should fire right when macros are done expanding
(exec (BEGIN-PROGRAM) 
  (, (INPUT $N $INPUT)
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
         
         (exec (TERM)
           (, (main eval (join (DONE $N_)) $OUTPUT)
           )
           (O (+ (OUTPUT $N_ $OUTPUT) )

              (- (main eval (join (DONE $N_)) $OUTPUT) )
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



";

}

const BOOLEAN_ALG_MULTI : &str ="

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

; (ctor bool 1)
; (ctor bool 0)
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))

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

; this should fire right when macros are done expanding
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
";

const BOOLEAN_ALG : &str ="

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

; (ctor bool 1)
; (ctor bool 0)
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))

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
     (MACRO ($name $proc $op) $pattern $template)
     
     (MACRO ($name main eval) $p $t)
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
";
// s.dump_sexpr(expr!(s, "[3] OUTPUT $ $"), expr!(s, "[3] OUTPUT _1 _2"), unsafe { out.as_mut_vec() });


// const BOOLEAN_ALG_MONOTONIC : &str ="

// (eval (and 0 0) -> 0)
// (eval (and 0 1) -> 0)
// (eval (and 1 0) -> 0)
// (eval (and 1 1) -> 1)

// (eval (or 0 0) -> 0)
// (eval (or 0 1) -> 1)
// (eval (or 1 0) -> 1)
// (eval (or 1 1) -> 1)

// (eval (if 0 0) -> 1)
// (eval (if 0 1) -> 1)
// (eval (if 1 0) -> 0)
// (eval (if 1 1) -> 1)

// (eval (not 0) -> 1)
// (eval (not 1) -> 0)

// (eval (0) -> 0)
// (eval (1) -> 1)

// ; (ctor bool 1)
// ; (ctor bool 0)
// ; (ctor bool-expr ($x))
// ; (ctor bool-expr (and $x $y))
// ; (ctor bool-expr (or  $x $y))
// ; (ctor bool-expr (xor $x $y))
// ; (ctor bool-expr (if  $x $y))

// (INPUT 0
//    (if (or (1) 
//            (not (and (or (1) (0))
//                      (1)
//                 )
//            )
//        )
//        (and (1) 
//             (or (0) (1))
//        )
//    )
// )
// (INPUT 1
//    (if (and (1) 
//             (or (0) (1))
//        )
//        (or (1) 
//            (not (and (or (1) (0))
//                      (1)
//                 )
//            )
//        )
//    )
// )

// ; case/0 
// (MACRO
//   (fork $proc $op)
//       (, ($proc $op (fork $ctx) ($case/0)) )
//       (, ($proc $op (join ($ctx case/0)) $case/0) )
// )
// ; case/1
// (MACRO
//   (fork $proc $op)
//       (, ($proc $op (fork $ctx) ($case/1 $x))
//       )
//       (, ($proc $op (fork ($ctx arg/0 )) $x     )
//          ($proc $op (join ($ctx case/1)) $case/1)
//       )
// )
// ; case/2
// (MACRO
//   (fork $proc $op)
//       (, ($proc $op (fork $ctx) ($case/2 $x $y))

//       )
//       (, ($proc $op (fork ($ctx arg/0 )) $x     )
//          ($proc $op (fork ($ctx arg/1 )) $y     )
//          ($proc $op (join ($ctx case/2)) $case/2)
//       )
// )


// ; case/0
// (MACRO
//   (join $proc $op)
//       (, ($proc $op (join ($ctx case/0)) $case/0)

//          ($op ($case/0) -> $out)
//       )
//       (, ($proc $op (join $ctx) $out) 
//       )
// )
// ; case/1
// (MACRO
//   (join $proc $op)
//       (, ($proc $op (join ($ctx case/1)) $case/1)
//          ($proc $op (join ($ctx arg/0)) $x)
         
//          ($op ($case/1 $x) -> $out)
//       )
//       (, ($proc $op (join $ctx) $out)
//       )
// )
// ; case/2
// (MACRO
//   (join $proc $op)
//       (, ($proc $op (join ($ctx case/2)) $case/2)
//          ($proc $op (join ($ctx arg/0 )) $x     )
//          ($proc $op (join ($ctx arg/1 )) $y     )

//          ($op ($case/2 $x $y) -> $out)
//       )
//       (, ($proc $op (join $ctx) $out)
//       )
// )



// ; the macro creates DEF, the MACROS are \"compiled out\"
// (exec (macro) 
//   (,
//      (MACRO ($name main eval) $p $t)
//   )
//   (, (DEF   ($name main eval) $p $t)
//   )
// )

// ; this should fire right when macros are done expanding
// (exec (BEGIN-PROGRAM) 
//   (, (INPUT $N $INPUT)
//   )
//   (,
//     (main eval (fork (DONE $N)) $INPUT)

//     (exec MAIN 
//       (, 
//          (DEF (fork main eval) $fork_p $fork_t)
//          (DEF (join main eval) $join_p $join_t)
         
//          (exec MAIN $main-pattern $main-template)
//       ) 
//       (, 
//          (exec (1 fork) $fork_p $fork_t) 
//          (exec (0 join) $join_p $join_t) 
         
//          (exec (TERM)
//            (, (main eval (join (DONE $N_)) $OUTPUT)
//            )
//            (O (+ (OUTPUT $N_ $OUTPUT) )

//               (- (main eval (join (DONE $N_)) $OUTPUT) )
//            )
//          )

//          (exec (RESET)
//            (, (main eval ($fork_join $ctx) $val)       )
//            (, (exec MAIN $main-pattern $main-template) )
//          )
//       )
//     )
//   )
// )
// ";
// // s.dump_sexpr(expr!(s, "[2] OUTPUT $"), expr!(s, "[2] OUTPUT _1"), unsafe { out.as_mut_vec() });


const BOOLEAN_ALG_SINGLE_INPUT_MONOTONIC : &str ="

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

; (ctor bool 1)
; (ctor bool 0)
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))

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
";
// s.dump_sexpr(expr!(s, "[2] OUTPUT $"), expr!(s, "[2] OUTPUT _1"), unsafe { out.as_mut_vec() });




const BOOLEAN_ALG_SINGLE_INPUT_MONOTONIC_NO_MACRO : &str ="

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

; (ctor bool 1)
; (ctor bool 0)
; (ctor bool-expr ($x))
; (ctor bool-expr (and $x $y))
; (ctor bool-expr (or  $x $y))
; (ctor bool-expr (xor $x $y))
; (ctor bool-expr (if  $x $y))

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
";
// s.dump_sexpr(expr!(s, "[2] OUTPUT $"), expr!(s, "[2] OUTPUT _1"), unsafe { out.as_mut_vec() });


const NAIVE_UNION : &str =
"
((symetric-difference ($in_a $in_b) -> $out)
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

(exec 0 (, ((symetric-difference (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
";

// use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
// use mork::space::{ParDataParser};
// use mork_expr::{Expr, ExprZipper};

// fn parse_sexpr(s: &Space, r: &[u8], buf: &mut [u8]) -> Result<(Expr, usize), ParserError> {
//     let mut it = Context::new(r);
//     let mut parser = ParDataParser::new(&s.sm);
//     let mut ez = ExprZipper::new(Expr { ptr: buf.as_mut_ptr() });
//     parser.sexpr(&mut it, &mut ez).map(|_| (Expr { ptr: buf.as_mut_ptr() }, ez.loc))
// }

// /// expects `sexpr` to be a tuple `(<pattern> <template>)`
// fn patten_template(s: &Space, sexpr : &str, parse_buf : &mut[u8]) -> Result<(Expr,Expr), ParserError> {
//     let (q_expr, _used) = parse_sexpr(&s, sexpr.as_bytes(), parse_buf)?;
//     let mut ez = ExprZipper::new(q_expr);
//     assert!( ez.next_child() );
//     let pattern =ez.subexpr();
//     assert!( ez.next_child() );
//     let template = ez.subexpr();
//     assert!( !ez.next_child() );
//     Ok( (pattern, template) )
// }

// fn import(s: &mut Space, pattern_template_sexpr: &str, import_data : &str) -> Result<(), ParserError> {
//   let mut parse_buf = [0;4000];
//   let (pattern, template) = patten_template(s, pattern_template_sexpr, &mut parse_buf)?;
//   s.add_sexpr(import_data.as_bytes(), pattern, template);
//   Ok(())
// }
// fn export<W:Write>(s: &Space, pattern_template_sexpr: &str, w: &mut W) -> Result<(), ParserError> {
//   let mut parse_buf = [0;4000];
//   let (pattern, template) = patten_template(s, pattern_template_sexpr, &mut parse_buf)?;
//   s.dump_sexpr(pattern, template, w);
//   Ok(())
// }

    #[test]
    fn test_2() -> std::io::Result<()>{
      // //////////
      // CONFIG //
      // ////////
      let input_file_path     = "/home/remyc/.trueai/MORK/minimal_metta_2_tutorial/Input.mm2";
      let output_file_path    = "/home/remyc/.trueai/MORK/minimal_metta_2_tutorial/Output.mm2";
      let trace_file_path     = "/home/remyc/.trueai/MORK/minimal_metta_2_tutorial/Trace.mm2";
      let iterations          = 1;
      let execs_per_iteration = 1;
      let do_trace            = true; // tracing happens once per iteration
      
      let (in_pattern,    in_template   ) = ("$", "_1"); // $x => $x
      let (out_pattern,   out_template  ) = ("$", "_1"); // $x => $x
      let (trace_pattern, trace_template) = ("$", "_1"); // $x => $x


      // ///////////////
      // THE PROGRAM //
      // /////////////

      let     in_file    = std::fs::File::open(input_file_path)?; 
      let mut out_file   = std::fs::File::options().create(true).write(true).open(output_file_path)?;
      let mut trace_file = std::fs::File::options().create(true).write(true).open(trace_file_path)?;

      // initialize the space
      let mut s = mork::space::Space::new();
      
      // IMPORT
      let input = std::io::read_to_string(&in_file)?;  
      s.add_sexpr(input.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"_1"));
      


      // run execs and traces
      let sys_time = || std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH);
      if do_trace {
         writeln!(trace_file, "; Begin Trace at time since UNIX_EPOCH : {:?}", sys_time())?;
      }
      for each in 0..iterations{
         if do_trace {
            writeln!(trace_file, "\n; State {}",each*execs_per_iteration)?;
            s.dump_sexpr(mork::expr!(s, trace_pattern), mork::expr!(s, trace_template), &mut trace_file);
         }
      
         s.metta_calculus(execs_per_iteration);
      }
      if do_trace {
         writeln!(trace_file, "\n; State {}",iterations*execs_per_iteration)?;
         s.dump_sexpr(mork::expr!(s, trace_pattern), mork::expr!(s, trace_template), &mut trace_file);
         writeln!(trace_file, "\n; End Trace at time since UNIX_EPOCH : {:?}\n", sys_time())?;
      }


      // EXPORT
      writeln!(out_file, "; Output at time since UNIX_EPOCH : {:?}", sys_time())?;
      s.dump_sexpr(mork::expr!(s, out_pattern), mork::expr!(s, out_template), &mut out_file);
      writeln!(out_file, "; End Output\n")?;
      Ok(())




        // let mut s = Space::new();


        // let file  = std::fs::File::open("/home/remyc/.trueai/MORK/minimal_metta_2_tutorial/Input.mm2").unwrap();
        // let input = std::io::read_to_string(&file).unwrap();
        // s.add_sexpr(input.as_bytes(), expr!(s,"$"), expr!(s,"_1"));


        // // s.add_sexpr(BOOLEAN_ALG_MULTI.as_bytes(), expr!(s,"$"), expr!(s,"_1"));

        // // for each in 0..100000 {
        // //     let str_ = format!("(INPUT {each:0>4} (if (or (1) (and (or (1) (0))(1) )) (and (1) (or (0) (1)))))\n");
        // //     s.add_sexpr(str_.as_bytes(), expr!(s,"$"), expr!(s,"_1"));
        // // }


        // // crate::utils::print_space(&s);
        // // crate::utils::print_sexpr_space(&s);
        
        // // let mut dummy = String::new();
        // // let start = std::time::Instant::now();
        // s.metta_calculus(1000);
        // // for _ in 0..300 {
        // //     std::io::stdin().read_line(&mut dummy);
        // //     s.metta_calculus(1);
            
        // //     println!("\n\n");
        // //     crate::utils::print_space(&s);
        // //     // crate::utils::print_sexpr_space(&s);
        // //     dummy.clear();
        // // }

        // // let end = start.elapsed();
        //     // crate::utils::print_space(&s);

        //     // crate::utils::print_sexpr_space(&s);

        // let mut out = std::fs::File::options().create(true).append(true).open("/home/remyc/.trueai/MORK/minimal_metta_2_tutorial/Output.mm2").unwrap();
        // write!(out, "; Output at time since UNIX_EPOCH : {:?}\n", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH));
        // s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), &mut out);
        // write!(out, "; End Output\n\n");

        // // let mut out = String::new();
        // // s.dump_sexpr(expr!(s, "$"), expr!(s, "_1"), unsafe { out.as_mut_vec() });
        // // s.dump_sexpr(expr!(s, "[3] OUTPUT $ $"), expr!(s, "[3] OUTPUT _1 _2"), unsafe { out.as_mut_vec() });
        // // s.dump_sexpr(expr!(s, "[2] OUTPUT $"), expr!(s, "[2] OUTPUT _1"), unsafe { out.as_mut_vec() });
        // // println!("{}",out);

        // // dbg!(end);
    }


    const BOOLEAN_ALG_BUGGY : &str ="
(_ (_ _) _ _)
(_ (_) _ _)

true

(exec _
  (,
     true
  ) 
  (,
     (____ _ (_) (_)) 
  )
)
";

    // #[test]
    // fn test_2_buggy(){
    //     let mut s = Space::new();
    //     s.add_sexpr(BOOLEAN_ALG_BUGGY.as_bytes(), expr!(s,"$"), expr!(s,"_1"));
    //         s.metta_calculus(10);
    // }    
}

pub(crate) mod utils;


fn main() {
    println!("Hello, world!");
}
