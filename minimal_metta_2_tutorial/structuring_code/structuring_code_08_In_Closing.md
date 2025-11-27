# Closing Remarks

Many important ideas have been covered here including:
- predication for separation of "names"
- execs
- sources
- sinks
- priorities
- unification
- set operations
- computing wide
- building a program
- macros for partial evaluation
- running multiple inputs
- running multiple programs

The examples have been chosen to give a non-trivial example strategies to expected issues people will encounter.
These strategies should give enough room to explore alternatives.

Some ideas that one could try:
- The path representation could be modified form this form
  ```
  ((.   case/2) and)
  (((.  arg/1 ) case/2) or)
  ((((. arg/1 ) arg/1 ) case/0) 1)
  ((((. arg/1 ) arg/2 ) case/0) 0)
  (((.  arg/2 ) case/2) if)
  ((((. arg/2 ) arg/1 ) case/0) 1)
  ((((. arg/2 ) arg/2 ) case/0) 1)
  ```
  to this
  ```
  ((((. (arg/1 and)) (arg/1 or)) case/0) 1)
  ((((. (arg/1 and)) (arg/2 or)) case/0) 0)
  ((((. (arg/2 and)) (arg/1 if)) case/0) 1)
  ((((. (arg/2 and)) (arg/2 if)) case/0) 1)
  ```
  How would the fork and join `DEF`s need to be modified for this change?

- Consider an input like this:
  ```
  (INPUT C
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
  ```
  Many of the branches have the same subtree.
  The following sub tree happens twice.
  ```
  (and ( or(1) (1))
       ( if(1) (1))
  )
  ```
  We could try to memoize the results; the right place to do so would be to
  save the results in a store available for all executions that want to share results. If we tried to implement this strategy, how effective would it be? (in the above case it might be far less effective than expected).

- We describe evaluating boolean expressions, which could be evaluated with short-cutting.
  Short-cutting is usually more interesting with side effects.
  Consider adding a side effects (writing to a shared global name for example) to the evaluation and modifying the code to make short-cutting work.
  One strategy would be to construct execs that are deferred and are only spawned conditionally.
  How does this affect the parallelism of the process?