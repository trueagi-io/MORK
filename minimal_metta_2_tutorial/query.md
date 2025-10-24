If you have see the section on data, then you will know that the "prefix" of an expression is important for indexing.

Fortunately this coincides well with adding user defined tags to attribute values
```
(animal cat)
(animal dog)
(animal bird)
(animal human)
(animal spider)

(mammal cat)
(mammal dog)
(mammal human)

(insect spider)

(aves bird)

(feet 4 cat)
(feet 4 dog)
(feet 2 bird)
(feet 2 human)
(feet 8 spider)
```




tags can also be used for namespacing.
```
(lib (boolean (type bool (+ true false))))

(lib (boolean (: OR  (-> (. bool bool) bool))))
(lib (boolean (= (OR true  true ) true )))
(lib (boolean (= (OR false false) true )))
(lib (boolean (= (OR false true ) true )))
(lib (boolean (= (OR true  false) false)))

(lib (boolean (: AND  (-> (. bool bool) bool))))
(lib (boolean (= (AND true  true ) true )))
(lib (boolean (= (AND false false) false)))
(lib (boolean (= (AND false true ) false)))
(lib (boolean (= (AND true  false) false)))

(lib (boolean (: NOT (-> (. bool) bool))))
(lib (boolean (= (NOT true)  false)))
(lib (boolean (= (NOT false) true)))
```

One might ask why aren't name spaces attributes? It's only a matter of convention.
```
((lib boolean)  (type bool (+ true false)))

((lib boolean)  (: OR  (-> (. bool bool) bool)))
((lib boolean)  (= (OR true  true ) true ))
((lib boolean)  (= (OR false false) true ))
((lib boolean)  (= (OR false true ) true ))
((lib boolean)  (= (OR true  false) false))

((lib boolean)  (: AND  (-> (. bool bool) bool)))
((lib boolean)  (= (AND true  true ) true ))
((lib boolean)  (= (AND false false) false))
((lib boolean)  (= (AND false true ) false))
((lib boolean)  (= (AND true  false) false))

((lib boolean)  (: NOT (-> (. bool) bool)))
((lib boolean)  (= (NOT true)  false))
((lib boolean)  (= (NOT false) true))
```