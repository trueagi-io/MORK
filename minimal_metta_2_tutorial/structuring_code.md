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
Sources come in Two variants,`(, ...)` and `(I ...)`























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


```





















