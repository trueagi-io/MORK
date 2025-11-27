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

We can see this pattern as an expression going out of scope.

Join can be modified similarly:
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
This looks more involved, but this is only because the 3 expressions we join, all go out of scope together.
It can be helpful to visually "brace" the scope by putting the value that will go out of scope at the top and bottom of the exec, with the rest of the transaction in the middle.

After putting all this together we 
run `./mork run Going_Wide_21_Larger_Programs.mm2`

Once again, try running with `--steps 0`, `--steps 1`, ... and so on.
This time focus on how the program is cleaning up after itself mid execution.
