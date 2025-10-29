<!-- https://github.com/trueagi-io/MORK/wiki/Space-Operations -->

# Relation algebra with MM2

Lets consider this simple dataset
```
(monster dragon)
(monster ogre)
(monster slime)
(monster skeleton)
(monster orc)
(monster ghost)
(monster centaur)

(animal horse)
(animal cat)
(animal dog)
(animal mouse)
(animal human)

((feet 2) human)
((feet 4) horse)
((feet 4) cat)
((feet 4) dog)
((feet 4) mouse)
((feet 0) slime)
((feet 2) ogre)
((feet 2) skeleton)
((feet 2) orc)
((feet 4) centaur)
```

we'll load it with a prefix
```
; pattern
$x
; template
(IN $x)
```






Set union
THIS IS WRONG
```
; a ∪ b
(set 
    (union ($out <- ($in_a $in_b))

        (, ($in_a $a)           
           ($in_b $b)
        )
        
        (, ($out $a)
           ($out $b)
        )
    )
)
```

set intersection
```
; a ∩ b
(set 
    (intersection 
        ($out <- ($in_a $in_b))
        (, ($in_a $a) 
           ($in_b $a)
        )
        (, ($out ($a $b))
        )
    )
)
```

Set difference
<!-- make a note about the requirement of a sink,
     if not careful, then not monotonic
-->
```
; a \ b
(set 
    (difference ($out <- ($in_a $in_b))
        (, ($in_a $a) 
           ($in_b $b)
        )
        (O (+ ($out $a))
           (- ($out $b))
        )
    )
)
```

cartesian product
<!-- make a note that for higher arities we need more versions -->

```
; a × b
(set
    (cartesian_product ($out <- ($in_a $in_b))
        (, ($in_a $a) 
           ($in_b $b)
        )
        (, ($out (x $a $b))
        )
    )
)
```


Projection
<!-- making this work on non triple stores seems hard to me. -->
```
; Π[atrribute](_)
(set
    ((projection $attribute) ($out <- $in)
        (, ($in  ($attribute $v))
        )
        (, ($out ($attribute $v))
        )
    )
)
```

