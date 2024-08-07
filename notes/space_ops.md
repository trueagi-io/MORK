## Space operations

TODO
- CHANGE RESTRICT SYMBOL
- BREAK UP PREFIX AND CARTESIAN
- ADD PREFIX DESTRUCT ALONG WITH PREFIX CONSTRUCT

### Composition
`x.y`

**Example**
From a logical perspective, a space `Foo.bar | Foo.baz | Foo.cux` can be represented more compactly as `Foo.(bar | baz | cux)`.
Likewise `(x | y | z).(a | b)` equals `x.a | y.a | z.a | x.b | y.b | z.b`.
For structures: `(Foo.(Bar | Baz)).(A.(1 | 2))` equals `Foo.(Bar.A.(1 | 2) | Baz.A.(1 | 2))`.

**Formula**
`{p.e | p∈x and e∈y}`

### Union
`x | y`

**Example**
A space containing a, b, and c is constructed via `a | b | c`

**Formula**
`{e | e∈x or e∈y}`

### Intersection
`x & y`

**Example**
When `x = a | b | c; y = a | c | e` then the result contains a and c

**Formula**
`{e | e∈x and e∈y}`
`{e | e∈x and ∃k∈y(e=k)}`

### Subtraction
`x \ y`

**Example**
When `x = a | b | c; y = c | e` then the result contains a and b

**Formula**
`{e | e∈x and e∉y}`

### Restriction
`x <| y`

**Example**
When `x = Foo.(Bar.(1 | 2 | 3) | Baz.(A | B | C) | Cux.(Red | Blue))`
     `y = Foo.(Bar | Baz)` then result is
     `Foo.(Bar.(1 | 2 | 3) | Baz.(A | B | C))`

**Formula**
read `x < y` as x is a prefix of y 
`{e | e∈x and ∃k∈y(e=k)}` <- intersection
`{e | e∈x and ∃p∈y(p ≤ e)}` <- restriction

**Explanation**
return each path "p" of left map 
 such that there exists a path in the right map that's a prefix of "p"

### Subspace
`s(p)`

**Example**
When `s = Foo.(Bar.(1 | 2 | 3) | Baz.(A | B | C))`
     `p = Foo.Baz` then result is
     `(A | B | C)`

**Formula**
`{e dropPrefix p | e∈s e hasPrefix p}`

### Drophead
`drophead s`

**Example**
When `s = Foo.(Bar.(1 | 2 | 3) | Baz.(A | B | C)) | Cuz.(A | B)` then result is
     `Bar.(1 | 2 | 3) | Baz.(A | B | C) | A | B`

**Formula**
`{e dropPrefix | e∈s}`

### Subsumption
`^ s`

**Formula**
`{e | e∈s and no e'∈s such that e' > e}`

### Instantiation
`v s`

**Formula**
`{e | e∈s and no e'∈s such that e' < e}`

### Sharing
`x ** y`

**Example**


**Intuition**
Like the GCD: Longest shared paths.

**Formula**
`{p sharedPrefix e | p∈x and e∈y and no p'∈x and e'∈y such that (p' sharedPrefix e') > (p sharedPrefix e)}`
`^ {p sharedPrefix e | p∈x and e∈y}`

**Laws**
`x = x <| (x ** y)`, `y = y <| (x ** y)`

### Transform
`x \p -> q`

**Signature** `Space x Path x Path -> Space`

**Example** 
When `x = Foo.(Bar.(1 | 2 | 3) | Baz.(A | B | C) | Cux.(Red | Blue))`
     `p = $_.Cux.$c`
     `q = Result.Color.$c` then the result is
     `Result.Color.Red | Result.Color.Blue`

**Formula**
`{r | e∈x and unify((e, r), (p, q))}`
