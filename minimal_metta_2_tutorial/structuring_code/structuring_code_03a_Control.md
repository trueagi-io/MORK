# Control
When a program runs one needs to have some control over evaluation.  
Code in the `Setup` | `Basics` | `Set_Ops` section have so far only required running MM2 for a very limited number of iterations.  
Despite this we have exerted a minor amount of "control" over the evaluation of our programs.  

With the advent of structured programming it was established that control flow for algorithms can understood through the lens of three major control constructs
- Sequence
- Selection
- Iteration

We will not pretend that MM2 is a "structured programming language" (MM2 is more in the family of process calculi), but we will use structured programming as means of comparison, and when useful find means to emulate it.

## Sequence
Sequencing in MM2 can be done with a combination of two properties:
- priority
- execs that spawn execs

### Priority Sequencing
Priority dictate which exec to run first.

Given the following program:
```
(exec 1 (, $x) (, 1))
(exec 0 (, $x) (, 0))
(exec 3 (, $x) (, 3))
(exec 2 (, $x) (, 2))
```

An ordering of all the priorities can be done from 0 to 3.
Each has been hardcoded to write out their priorities when they successfully execute.

run for all steps in 0 to 3 inclusive
```sh
./mork run --steps 0 Control_Priority_Seq.mm2
./mork run --steps 1 Control_Priority_Seq.mm2
./mork run --steps 2 Control_Priority_Seq.mm2
./mork run --steps 3 Control_Priority_Seq.mm2
```

Using the MORK CLI as we have so far, the ordering is deterministic. For each step amount, the writes will sequence in the expected way.  


### Execs chain sequencing

Another way to Sequence operations is to have an exec spawn another exec as one of it's outputs.
```
(exec 0 (, $x)
        (, 0
           (exec 0 (, 0)
                   (, 1
                      (exec 0 (, 1) 
                              (, 2
                                 (exec 0 (, 2)
                                         (, 3)
                                 )
                              )
                      )
                   )
           )
        )
)
```

Here each exec writes a value, spawns the next.
Each exec will run if the patterns succeed:
- the first one will succeed as it matches itself
- The ones that follow will succeed as they match the value of the previous write.

run for all steps in 0 to 3 inclusive
```sh
./mork run --steps 0 Control_Exec_Chaining_Seq.mm2
./mork run --steps 1 Control_Exec_Chaining_Seq.mm2
./mork run --steps 2 Control_Exec_Chaining_Seq.mm2
./mork run --steps 3 Control_Exec_Chaining_Seq.mm2
``` 

This causes a sequencing. The exact method of generating an exec (by hardcoding, or matching a "definition") does not matter.

In contrast to priorities, the ordering is _dependant_ on a previous exec successfully running.

We can modify the code such that a spawned exec fails to match (in this case instead of it will fail to find `!`)
```
(exec 0 (, $x)
        (, 0
           (exec 0 (, !)
                   (, 1
                      (exec 0 (, !)
                              (, 2
                                 (exec 0 (, !)
                                         (, 3)
                                 )
                              )
                      )
                   )
           )
        )
)
```
run for all steps in 0 to 1 inclusive
```sh
./mork run --steps 0 Control_Exec_Chaining_Fail_Seq.mm2
./mork run --steps 1 Control_Exec_Chaining_Fail_Seq.mm2
``` 
The first exec will run, but the second one will fail, and disappear.

## Selection
Execs have a built in means of selection via pattern matching.

```
(case b)
(case c)
(exec 0 (, (case a)) (, a))
(exec 0 (, (case b)) (, b))
(exec 0 (, (case c)) (, c))
```
run `./mork run Control_Select_b_c.mm2`

We can try to run all cases, and we select `(case b)` and `(case c)`.

An alternative would be to "match first".
There are dual ways of doing this.
The first is to remove the data that would be matched.
```
(case b)
(case c)
(exec 0 (, (case a) (case $x)) (O (+ a) (- (case $x) )))
(exec 0 (, (case b) (case $x)) (O (+ b) (- (case $x) )))
(exec 0 (, (case c) (case $x)) (O (+ c) (- (case $x) )))
```
run `./mork run Control_Select_First_Data.mm2`

outputs `b`

The other would be to remove the execs that would match
```
(case b)
(case c)
(exec 0 (, (case a) (exec 0 $p $t)) (O (+ a) (- (exec 0 $p $t) )))
(exec 0 (, (case b) (exec 0 $p $t)) (O (+ b) (- (exec 0 $p $t) )))
(exec 0 (, (case c) (exec 0 $p $t)) (O (+ c) (- (exec 0 $p $t) )))


(exec 1 (, $x) (, (Ran After)))
```
run `./mork run Control_Select_First_Exec.mm2`

An extra exec has been added to show that we only removed execs of a given priority.

outputs
```
(Ran After)
(case b)
(case c)
b
```

## Iteration

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

Iteration was done using recursion, on closer inspection we see that recursion was done by our second sequencing technique, exec chaining.

In some sense the actual thing iterating is the runtime itself.

## Halt Iteration with Sequencing and Selection

The issue is that we want most sub-programs to halt. We can do this by selection failure. Selection failure exhausts the exec, ending the loop.  

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
run `./mork run --steps 0 Control_Halts_on_fail.mm2`
you should find this
```
(counter (S (S Z)))
(exec LOOP (, (counter (S $a)) (exec LOOP $b $c)) (O (+ (exec 0 $b $c)) (+ (counter $a)) (- (counter (S $a)))))
```
the counter decremented by one Peano successor.

Every time we sequence by chaining the exec, we modify the state such that we converge to failure.

When the match fails at `(counter Z)`, the exec will be exhausted without making any writes, so it wont write itself back

Another alternative is to spawn other execs with higher priority, and it would do the opposite, It would run every in an unbounded way, expecting one of the spawned execs to fail until it matches; that exec would then be responsible to remove the looping exec.
```
(counter (S (S (S Z))))
(exec (LOOP 9) 
   (, (exec (LOOP 9) $p $t) )
   (O  
       (+ (exec (LOOP 1) 
            (, (counter (S $x)) ) 
            (O 
               (+ (counter $x)     )
               (- (counter (S $x)) )
            )
          )
       )
       (+ (exec (LOOP 0) 
            (, (exec (LOOP $n) $_p $_t)
               (counter Z) 
            )
            (O (- (exec (LOOP $n) $_p $_t) ))
          )
       )
       (+ (exec (LOOP 9) $p $t))
   )
)
```

----

The rest of this section 

----


# Multithreaded concurrent/parallel execution
We won't be doing any multithreading in this tutorial, but talking about is important, as the code structure that is presented takes this consideration into account.

In the following I will sometimes use the term transaction to mean the running of an exec.

## Structure of Multithreaded Execs
In a multithreaded setting we have a constraint on the structure of execs.
```
(exec (<THREAD_ID> <PRIORITY>) <SOURCES> <SINKS>)
```
`(<THREAD_ID> <PRIORITY>)` is required to be ground (not contain variables).

The runtime then uses predication enforce a thread prefix.
(prefixes are mentioned in [Data in Mork](https://github.com/trueagi-io/MORK/wiki/Data-in-MORK))

The thread prefix for a `<THREAD_ID>` of `thread-1` looks like this:  
`(exec (thread-1 $<PRIORITY>) $<SOURCES> $<SINKS>)`

The runtime sees it like this (where `[_]` is an arity tag):
`[4] exec [2] thread-1`

Once a thread starts running nothing can be written to that prefix other than that thread.

Priority is then a "thread local" property rather than a global one.

### Permission Prefixes

Prefixes are used as a permission to read an write a part of the global state. Threads then race to acquire permissions for their transactions.
Sources behave as readers, and Sinks as writers. Threads can share reads, but not writes. 
The runtime derives "constant" prefixes dynamically to keep contention as low as possible.

As an example:
```
(exec (thread-1 0) (, (path-file (((/ home) / code) / mork) $x) 
                      (extension .mm2 $x)
                   )
                   (, (.mm2 $x)
                   )
)
```
Thread prefix
- `[4] exec [2] thread-1` 
Priority
- `0` 
Read permission prefixes
- `[3] path-file [3] [3] [2] / home / code / mork`
- `[3] extension .mm2`
Write permission prefix
- `[2] .mm2`

Note how the permission prefixes stop before the variable.
If we had a reverse index of `path-file` called `file-path` and used that instead to get the filename:
```
(file-path $x (((/ home) / code) / mork)) 
```
the derived read permission prefix would be:
- `[3] file-path`
The fact that it is shorter is very important; more of the global state will be in-accessible for writes (everything below that prefix) until the transaction is complete.

Within a transaction, reads and writes can have overlapping permissions.  

It is therefore possible to reason about the behavior as follows:
- Look up next exec in current thread (biased by Priority)
- Derive the the set of read and write permissions prefixes.
- _Attempt_ to acquire all needed permissions for the transaction.
  - If successful, transact
    - make reads
    - release read permissions when reads are complete
    - run with write permissions
    - release write permissions on completion of transaction
    - Reset Priority to top
  - On failure defer current transaction

## Writing Multithreaded Oblivious code
One could write all single threaded priorities as pairs in the `(<THREAD_ID> <PRIORITY>)` form and the single threaded behavior would be equivalent.


### Sequential footguns

Using multithreaded concurrent/parallel execution (like in the server branch) the priority does not guarantee determinism, Priority still determines which execs will _attempt_ to run first.
If an exec cannot run (cannot acquire read/write permissions yet), it is not exhausted, instead it is deferred, and the next highest priority is attempted.  
This is why it is a _priority_ and not a _sequence_.  

To write MM2 in a way that will work in both single-threaded and multi-threaded context correctly, one cannot simply rely on solely on priorities for sequencing.

Working with exec chaining alone won't be enough either.  
Using multithreaded concurrent/parallel execution we would have to consider the following case.

We would like to have these 2 threads communicate do do work together.
```
; guarantees execution of initial execs
t

; thread 1
(exec (thread-1 0) (, t)
                   (, 
                      (t 1)
                      (exec (thread-1 0) (, (t 2)   ) 
                                         (, (t 2 1) )
                      )
                   )
)

; thread 2
(exec (thread-2 0) (, t) 
                   (, 
                      (t 2)
                      (exec (thread-2 0) (, (t 1)   )   
                                         (, (t 1 2) )
                      )
                   )
)
```
Ideally they would both run, `thread-1` and `thread-2` would write `(t 1)` and `(t 2)` at the same time.
Then the spawned execs would both expect to see each other's message,  
and then they would both write `(t 2 1)` and `(t 1 2)` respectively.

The desired output
```
(t 1)
(t 2)
(t 1 2)
(t 2 1)
t
```
But let's try to run this single threaded.

run 
```sh
./mork run --steps 2 Control_Exec_Race_Seq.mm2
``` 
we get this output
```
(t 1)
(exec (thread-2 0) (, t) (, (t 2) (exec (thread-2 0) (, (t 1)) (, (t 1 2)))))
t
```

We find that `thread-1` failed to find `(t 2)` with it's spawned exec. It then exhausted itself.

In this simulation, `thread-2` hasn't made progress yet.
Once it finally does, our output will be "incomplete", missing `(t 2 1)`.
```
(t 1)
(t 2)
(t 1 2)
t
```

### Shared State, Private state
It should be clear that the the issue with permissions has to do with sharing. Any form of shared information can cause a sequence to fail.

Either because a transaction
- was delayed by a permission failure
- ran prematurely exhausting itself

A convention would be needed to predicate what part of the global space is private to a thread. It could be as simple as having a predication of this form:
- `(thread-local <THREAD_ID> <LOCAL_DATA>)`
given that a `<THREAD_ID>` is ground the derived prefix would be
- `[3] thread-local <THREAD_ID>`

So long as threads only read/write to their own id, this is effective.

This _almost_ guarantees sequencing by itself if a thread only accesses local data.

_Almost_ as one might be tempted to debug programs by reading from a running thread's locals. That read can interfere with the sequence, by permission failure, when the thread tries to write at that prefix. 

This would guarantee however that a thread can store things like program counters, state labels.

Once a program counter or a state label has been changed, execs can be engineered to go from succeeding to match, to failing to match local state. This includes recursive execs...

### Ordered Cycles
The solution to the issue is reintroduce determinism with loops using temporal logic.

In temporal logic we can describe two temporal quantifiers, "Always" and "Eventually" (as in "Always the case" and "Eventually the case").

We abbreviate
- "Always" to "[]" (a box).
- "Eventually" to "<>" (a diamond)

We can use this language to describe progress in a system:
- Eventually the counter reaches 0  
  ```
  <>( counter = 0 )
  ```
- Always the case that when the counter is not equal to 0, the next state of counter is counter - 1 
  ```
  [](  counter =/= 0 
    => counter' = counter - 1
    )
  ```
- We can combine these with logical and to describe a _behavior_:  
  - Counter is not negative
  - Always the case that when counter is not 0, the next state of the counter is counter - 1
  - Eventually the counter is 0
  ```
      (counter >= 0)
  AND [](  counter =/= 0 
        => counter' = counter - 1
        )
  AND <>( counter = 0 )
  ```

A powerful way to use these is actually to use both on the same specification.
- `<>[]` Eventually always the case
- `[]<>` Always eventually the case

We can try to understand our programs by visualizing them as graphs.

Here is a sequence from to state to state (s), with a series of actions (a).
```
s0 --a0--> s1 --a1--> s2
```

Here is a sequence entering a loop, then exitig a loop.
```
            +---> a1 ---+
            |           |
            |           v
s0 --a0--> s1           s2 --a3--> s3
            ^           |
            |           |
            +--- a2 <---+
```

Let's assume we _always_ start at state `s0` and all actions are tried in a given order (when an action is not associated to a state it is ignored);  
so long as `a0` appears __once__ in the stream of actions,  
_eventually_ we will transition to state `s1`.
```
[]<>(state = s1)
```
For this to be true we only need to reach `s1` once.

We just need to guarantee that when `a0` runs, it runs completely without interruption, this is called atomicity.

This is also true for `s2`.
```
    []<>(state = s1)
AND []<>(state = s2)
```

Same as before for `a1`, it needs only appear __once__ in the stream of actions.

Transactions are atomic, so if they run, they run completely.
If there was a transaction that regularly is given a chance to run, should eventually run.

Using the above can we say the same for reaching `s3`?
No. The given order has not been specified enough. It may just loop back and forth between `s1` and `s2`.

What we can do is make the atomic action of `a1` cause the next action of `a3` to become more likely.

we'll now pair our previous machine with another another one. We'll then require actions to only run, if it can run on both machines.

```
            +---> a1 ---+
            |           |
            |           v
s0 --a0--> s1           s2 --a3--> s3
            ^           |
            |           |
            +--- a2 <---+


 t0 --a1--> t1 --a1--> t2 -a1-> t3 --a3-->
/ ^        / ^        / ^
| |        | |        | |
{a0,a2,a3} {a0,a2,a3} {a0,a2,a3}
```

We can now see that so long as both machines move in lockstep, the second machine (t) will limit the number of times `a1` is run, and avoid running `a2` after. We guarantee that after this point, if `a3` happens at least __once__, we will eventually get to state `s3`.

It would now be possible to reason that `[]<>(state = s3)`

Since there is nowhere to go after `s3`, trivially stalling `<>[](state = s3)`

What does this look like in MM2?
```
(thread-local thread-1 (state-s s0))
(thread-local thread-1 (state-t t0))

(exec (thread-1 0)
   (, )
)
```



