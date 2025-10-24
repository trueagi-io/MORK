MORK is an extremely flexible system, where that flexibility means that
other kinds of databases can be emulated trivially.

We will begin with a simple use case for MM2.
Let us imagine having a triple store.
Triple stores are an interesting case as they are very simple for
people understand at a high level, but are notoriously hard as it is inherently dynamic.




Set union
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
        ; (E A V)
        ; (V A E)
        (, ($in  ($attribute $v))
        )
        (, ($out ($attribute $v))
        )
    )
)
```

