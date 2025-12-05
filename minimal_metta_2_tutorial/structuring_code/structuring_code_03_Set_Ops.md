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
run `./mork run --steps 0 Set_Ops_01_Hardcoded_Locations.mm2`

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
Not bad!

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
run `./mork run --steps 1 Set_Ops_02_Parameterized_Locations.mm2`

This works!

Let's break down why.
The main workhorse here is _unification_.

## Unification
Unification is a form of bidirectional pattern matching.

Unification either fails to match, or succeeds to find the "Most General Unifier", the MGU.
The MGU is a substitution set that if applied to either argument will
result in the same value.

Let's examine some example arguments and results
```
unify : (1 2) (1 2)
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

We now have enough intuition to see how the union definition works.

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
(In this case look at the `$in_a` `$in_b` and `$out` in `$p` and `$t`)
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
We see what `$p` and `$t` are now.
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
run `./mork run --steps 0 Set_Ops_02_Parameterized_Locations.mm2` and see the result.

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
The exec using the definition.
```
(exec 0 (, ((union (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```

run `./mork run Set_Ops_03_Union.mm2`

After consuming the exec, it will leave behind these new values.
```
(ret a)
(ret b)
(ret c)
(ret d)
```

## Intersection

For intersection we need to have the __constraint__ that both argument elements are the same value.
```
((intersection ($in_a $in_b) -> $out)
    (, ($in_a $a)           
       ($in_b $a)
    )
    (, ($out $a) )
)
```
The exec using the definition.
```
(exec 0 (, ((intersection (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
run `./mork run Set_Ops_04_Intersection.mm2`

After consuming the exec, it will leave behind these new values.
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
The exec using the definition.
```
(exec 0 (, ((difference (arg_a arg_b) -> ret) $p $t) )
        (, (exec 0 $p $t) )
)
```
run `./mork run Set_Ops_05_Difference.mm2`

After consuming the exec, it will leave behind these new values.
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
run `./mork run Set_Ops_06_Symmetric_Difference.mm2`

after consuming the exec, it will leave behind these new values
```
(ret a)
(ret d)
```

# Closing on Set operations

Generally these operations need not be defined, rather they should be understood.
Set operations are implicitly happening every time you run an exec.
More sophisticated actions are usually subtle variations of these examples above, with more domain specific behavior.

----

Next we start building a more involved program in `structuring_code_04_Going_Wide.md`.
