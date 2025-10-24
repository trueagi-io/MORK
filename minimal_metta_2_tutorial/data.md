In MM2 there are various data-types. Users interact with the internal data types
with a `.mm2` file format, it is a human readable sub-set of a `.metta` file.

The subset comes from a low level detail with the encoding of S-expression to
the internal representation.

Let's look at some valid `.mm2` code that is part of that subset.

```
; A comment, everything after this till the next newline is ignored by the parser.
; comments must be outside of an S-expression

true
2
"abc def"
$x
(abc def) 
(abc (d e f))
($x $x)
(a "
" b)
```

## S-Expression Representation

Let's have a peak at the current representation of S-expressions inside MORK. Formatting has been added to make it easier to see at a glace, but it is still representing a byte string.
```
[Tag(Arity(2)), Tag(NewVar), 
                Tag(VarRef(0))
]
[Tag(Arity(2)), Tag(SymbolSize(3)), Byte(97), Byte(98), Byte(99),
                Tag(Arity(3)), Tag(SymbolSize(1)), Byte(100), 
                               Tag(SymbolSize(1)), Byte(101), 
                               Tag(SymbolSize(1)), Byte(102)
]
[Tag(Arity(3)), Tag(SymbolSize(1)), Byte(97), 
                Tag(SymbolSize(3)), Byte(34), Byte(10), Byte(34),
                Tag(SymbolSize(1)), Byte(98)
]
[Tag(Arity(2)), Tag(SymbolSize(3)), Byte(97), Byte(98), Byte(99),
                Tag(SymbolSize(3)), Byte(100), Byte(101), Byte(102)
]
[Tag(NewVar)]
[Tag(SymbolSize(1)), Byte(50)]
[Tag(SymbolSize(4)), Byte(116), Byte(114), Byte(117), Byte(101)]
[Tag(SymbolSize(9)), Byte(34), Byte(97), Byte(98), Byte(99), Byte(32), Byte(100), Byte(101), Byte(102), Byte(34)]
```
Each value in this lists represents one byte. it might be a little daunting to look at first, but we can already see some basic types.

Tagged
- structural
  - Tag(Arity(_))
  - Tag(SymbolSize(_))
- variables
  - Tag(NewVar)
  - Tag(VarRef)

Untagged raw bytes
- Byte(_)


Here is a more compact form for the tags:
- `Tag(Arity(_))      => [_]`
- `Tag(SymbolSize(_)) => <_>`
- `Tag(NewVar)        => $`
- `Tag(VarRef(_))     => &_`

And a more "transparent" representation of the bytes, that shows the unicode scalar value and hex:
- `Byte(b'a') => {'a'x61}`

You should now start to see some of the S-expressions that we had (they have been added for side by side comparison).
```
; (  $x $x)
  [2] $ &0
  
; (abc (d e f))
  [2] <3> {'a'x61} {'b'x62} {'c'x63} [3] <1> {'d'x64} <1> {'e'x65} <1> {'f'x66}
  
; (abc def) 
  [2] <3> {'a'x61} {'b'x62} {'c'x63} <3> {'d'x64} {'e'x65} {'f'x66}

; (a "\n" b)
  [3] <1> {'a'x61} <3> {'"'x22} {'\n'x0a} {'"'x22} <1> {'b'x62}

; $x
  $

;  2
  <1> {'2'x32}

; true
  <4> {'t'x74} {'r'x72} {'u'x75} {'e'x65}

; "abc def"
  <9> {'"'x22} {'a'x61} {'b'x62} {'c'x63} {' 'x20} {'d'x64} {'e'x65} {'f'x66} {'"'x22}
```


This representation is subject to change, but the broad strokes are not.
There are :
- Atomic values (for now symbol encompasses all of these),
  - You might be surprised to see `{'"'x22}` as a represented byte in the current implementation.
- Variables are described in two parts:
  - where they are bound,
    - note how variables are stripped of their names
  - where they are referenced.
    - note variable references are relative to the total number of introduced bindings to the left, this is called De Bruijn levels (related, but not to be confused with De Bruijn indices which are _relative_ to the most recent bindings to the left)
    - given the above notation `[2] &0 $` would be a syntax error, as the reference is before the binding.

- Data structure is described in polish notation, by an arity byte. 

Lets break this down, starting with polish notation.
Lets look at this example (the hex will be removed for clarity).
```
; (abc (d e f))
  [2] <3> {'a'} {'b'} {'c'} 
      [3] <1> {'d'} 
          <1> {'e'} 
          <1> {'f'}
```
Polish notation works by using operators of fixed arity and building an expression from
back to front. We could interpret our encoding above using a stack. (We will push to the front)
Here are actions : 
- `{_} => push(_)`
- `$   => push($)`
- `&_  => push(&_)`
- `<_> => len_n_sym(_)`
- `[_] => arity_n_tuple(_)`

Don't stare too long, just try to see the overall pattern.
```
DO

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> {'d'} <1> {'e'} <1> {'f'}
stack  : ['f']

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> {'d'} <1> {'e'} <1> _____
stack  : [f]

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> {'d'} <1> {'e'} ___ _____
stack  : ['e', f]

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> {'d'} <1> _____ ___ _____
stack  : [e, f]

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> {'d'} ___ _____ ___ _____
stack  : ['d', e, f]

code   : [2] <3> {'a'} {'b'} {'c'} [3] <1> _____ ___ _____ ___ _____
stack  : [d, e, f]

code   : [2] <3> {'a'} {'b'} {'c'} [3] ___ _____ ___ _____ ___ _____
stack  : [(d e f)]

code   : [2] <3> {'a'} {'b'} {'c'} ___ ___ _____ ___ _____ ___ _____
stack  : ['c', (d e f)]

code   : [2] <3> {'a'} {'b'} _____ ___ ___ _____ ___ _____ ___ _____
stack  : ['b', 'c', (d e f)]

code   : [2] <3> {'a'} _____ _____ ___ ___ _____ ___ _____ ___ _____
stack  : ['a', 'b', 'c', (d e f)]

code   : [2] <3> _____ _____ _____ ___ ___ _____ ___ _____ ___ _____
stack  : [abc, (d e f)]

code   : [2] ___ _____ _____ _____ ___ ___ _____ ___ _____ ___ _____
stack  : [(abc (d e f))]

DONE
```

Normally the purpose of Polish notation is to obviate parenthesis, made popular by its reverse version in HP calculators and the Forth programming language, often the backbone of simple virtual machines.

But you might have noticed, we can't be building expressions back to front, we have untagged bytes!
MORK actually uses the dual property; __assuming the expression is well constructed__, we will know how much left there is to traverse.
In other words, context is at the "prefix" of an expression.

As untagged bytes cannot be used for understanding structure (and cannot be bound to variables) we will skip the untagged bytes steps.
We will also dispose of the braces.

Let's visualize this:
```
DO

bytes   : [2] ...
prefix  : [2]
partial : (_ _)

bytes   : [2] <3> 'a' 'b' 'c' ...
prefix  : [2] abc
partial : (abc _)

bytes   : [2] <3> 'a' 'b' 'c' [3] ...
prefix  : [2] abc [3]
partial : (abc (_ _ _))

bytes   : [2] <3> 'a' 'b' 'c' [3] <1> 'd' ...
prefix  : [2] abc [3] d
partial : (abc (d _ _))

bytes   : [2] <3> 'a' 'b' 'c' [3] <1> 'd' <1> 'e' ...
prefix  : [2] abc [3] d e
partial : (abc (d e _))

bytes   : [2] <3> 'a' 'b' 'c' [3] <1> 'd' <1> 'e' <1> 'f'
prefix  : [2] abc [3] d e f
partial : (abc (d e f))

DONE
```

One might wonder, is it possible to represent these "prefix" values with S-expressions?

The answer is yes!

In the general case is a little tedious, but at least it is straightforward and mechanical.

If one wants to represent this prefix `(abc (d _ _))` replace the `_` with free variables 
(Make sure they are distinct! Otherwise, it isn't a prefix, it's a constraint; more on unification later.)
- `(abc (d $x $y))`

The internal representation will be like so:
- `[2] <3> 'a' 'b' 'c' [3] <1> 'd' $ $`
or more concisely:
- `[2] abc [2] d $ $`

So long as the trailing values are free variables this effectively represents a prefix.

For now we will finish by stating that s-expressions have a _biased_ representation in MORK.
In general, you want to construct values with a "ground" prefix, and defer variables to the suffix.
This correlates directly the how well MORK can index your values.

But what are we indexing into?

## The Space of expressions as a Pathmap
The primary backing data structure of MORK is a 256 radix trie. 256 is not a coincidence, it represents 1 byte.

I'll describe briefly what a radix trie is.

Radix tries are often used for things like auto-completion of text. Say I make a small set of words ...
```
abc
app
appease
apple
application

before
beta
```

... and I look up in the small set of words by writing some starting characters, the auto-complete may make suggestions
based on the prefix.

'a'
```
a |> bc
  |> pp
  |> ppease
  |> pple
  |> pplication
```

'p'
```
ap |> p
   |> pease
   |> ple
   |> plication
```

write another character 'l' (that is not a in the set)
```
apl |?
   
```

oops, backspace
```
ap |> p
   |> pease
   |> ple
   |> plication
```

'p'
```
app |! 
    |> ease
    |> le
    |> lication
```

'l'
```
appl |> e
     |> ication
```

'i'
```
appli |> cation
```

Past this point the value must be "application", or outside our small set.
If we accept this, then we have a match.

Let's revisit when we put in the second 'p'.

We can see that "app" is our index into the set of words, but it is not necessarily a complete word yet, just a prefix.
The suffix holds a set of suffixes af a search tree.

The search tree is made up of nodes like this (abstractly...).
```
[ 'a' -> [ 'b' -> "c" -> .
         | 'p' ->  "p" -> [ ""  -> .
                          | 'e' -> "ase" -> .
                          | 'l' -> [ 'e' -> .
                                   | 'i' -> "cation" -> .
                                   ]
                          ]
         ]
|   
   'b' -> "e" -> [ 'f' -> "ore" -> .
                 | 't' -> "a" -> .
                 ]
]
```
To make the following explanation simpler, we give these abstract trees "memory addresses"; it is now clear we have variant of an adjacency map. 
```
&0  : .

&1  : [ 'a' -> &2 | 'b' -> &9 ]

&2  : [ 'b' -> &3 | 'p' -> &4 ]

&3  : "c" -> &0

&4  : "p" -> &5

&5  : [ "" -> &0 | 'e' -> &6 | 'l' -> &7 ]

&6  : "ase" -> &0

&7  : [ 'e' -> &0 | 'i' -> &8 ]

&8  : "cation" -> &0

&9  : "e" -> &10

&10 : [ 'f' -> &11 | 't' -> &12 ]

&11 : "ore" -> &0

&12 : "a" -> &0
```

Now if we think about what we did earlier, we had to remember where we were when we did a backspace, otherwise we would
need to reindex the entire space from the beginning.
This is why I made the addresses above. They will help us in describing the history of our indexing, it will be represented as a stack (push back).

Let's do a trace.
```
where root : &1

+---------------------------------+------------+-----------------+-------------------------------+
|  stimulus                       |  focus     |  path           |  history                      |
+---------------------------------+------------+-----------------+-------------------------------+
:  init                           :  Some(&1)  :  ""             :  []                           :
:  'a'       -> descend('a')      :  Some(&2)  :  "a"            :  [radix(&1)]                  :
:  'p'       -> descend('p')      :  Some(&4)  :  "ap"           :  [ .. , radix(&2)]            :
:  'l'       -> fail('l')         :  None      :  "apl"          :  [ .. , fail(Some(&4), 'l')]  :
:  backspace -> ascend(1)         :  Some(&4)  :  "ap"           :  [ .. , radix(&2)]            :
:  'p'       -> descend('p')      :  Some(&5)  :  "app"          :  [ .. , string(&4, 1)]        :
:  'l'       -> descend('l')      :  Some(&7)  :  "appl"         :  [ .. , radix(&5)]            :
:  'i'       -> descend('i')      :  Some(&8)  :  "appli"        :  [ .. , radix(&7)]            :
:  enter     -> descend_to_val()  :  Some(&0)  :  "application"  :  [ .. , string(&8, 6)]        :
+---------------------------------+------------+-----------------+-------------------------------+

final state of: 
    path    : "application"
    history : [radix(&1), radix(&2), string(&4, 1), radix(&5), radix(&7), string(&8, 6)]
                  'a'        'p'        "p"            'l'        'i'       "cation"
```

The state with associated stimuli we have described above is a "zipper".

If you take everything you have seen so far with the byte representation of S-expressions, try to see that plainly as byte strings into
a radix trie, where one byte represents a radix separation.

This is not a user facing part of MORK, but it gives context as to why a program can be fast or slow in MORK.
The zipper allows reasoning about sets where prefixes are a filter of the set of all expressions, and 
"suffixes" as sets to complete an expression, by only having a handle to the "root of a suffix tree".

Lets look at our earlier set of S-expressions as in the internal expr representation
```
; ($x $x)
; (abc (d e f))
; (abc def) 
; (a "\n" b)
; $x
;  2
; true
; "abc def"

  [2] $ &0
  [2] <3> 'a' 'b' 'c' [3] <1> 'd' <1> 'e' <1> 'f'
  [2] <3> 'a' 'b' 'c' <3> 'd' 'e' 'f'
  [3] <1> 'a' <3> '"' '\n' '"' <1> 'b'
  $
  <1> '2'
  <4> 't' 'r' 'u' 'e'
  <9> '"' 'a' 'b' 'c' ' ' 'd' 'e' 'f' '"'
```

You should be able to see the trie. (to compress, a symbol with quotes is unescaped, but the bytes following a symbol with tag striped is prefixed with 'b')
```
[  [2]   -> [  $     ->   &0
            |  <3>   ->   b"abc" -> [  [3]  ->  d e f
                                    |  <3>  ->  b"def"
                                    ]
            ]
|  [3]   ->  a "\n" b
|  $       
|  <1>   ->  b"2"
|  <4>   ->  b"true"
|  <9>   ->  b"\"abc def\""
]
```
Under the assumption that comparison of a byte is fast, and comparing strings of contiguous bytes is fast, 
candidate sets of values are quickly filtered.

## Constraints on MM2 data types
One might wonder why `.mm2` files are a subset of `.metta` files.
This comes back to the tag byte encoding.

If the tag is a single byte, then we know from the outset that there can only be 256 variants at most.
Once again what follows is based on the current implementation, but it helps to understand by enumerating.

There are tags that the internals need extract out a number from, in order to parse what follows.
- `0b_00_.._.._..` Arity ((where the remaining bits are the arity , `0..=63`))
- `0b_01_.._.._..` (reserved for future use)
- `0b_10_.._.._..` VarRef (where the remaining bits are a De Bruijn level , `0..=63`)
- `0b_11_.._.._..` Symbol or NewVar  
  - `0b_11_00_00_00` New Variable
  -  otherwise Symbol (where the remaining bits are a _non-zero_ length, `1..=63`)

The variants have a primary discriminant, we need at least a nibble (two bits). This means the "magic number" is <= 64, where Symbols of length zero cannot exist.

In practice this should be very expressive. But it is still technically a subset.

Let's look at some limiting cases
```
; ; the following is too big
; the arity required is 64, but only up to 63 is supported
; (
;   00 01 02 03 04 05 06 07 08 09
;   10 11 12 13 14 15 16 17 18 19
;   20 21 22 23 24 25 26 27 28 29
;   30 31 32 33 34 35 36 37 38 39
;   40 41 42 43 44 45 46 47 48 49
;   50 51 52 53 54 55 56 57 58 59
;   60 61 62 63
; )

; but this is fine however as it is now an arity 10, well below 63.
( (00 01 02 03 04 05 06 07 08 09)
  (10 11 12 13 14 15 16 17 18 19)
  (20 21 22 23 24 25 26 27 28 29)
  (30 31 32 33 34 35 36 37 38 39)
  (40 41 42 43 44 45 46 47 48 49)
  (50 51 52 53 54 55 56 57 58 59)
  (60 61 62 63 64 65 66 67 68 69)
  (70 71 72 73 74 75 76 77 78 79)
  (80 81 82 83 84 85 86 87 88 89)
  (90 91 92 93 94 95 96 97 98 99)
)
```

Variables have different limitation:
```
; This wont work, it requires 65 variables, but the limit is 64.
; ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
;   ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
;   ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
;   ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
;   ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
;   ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
;   ($x60 $x61 $x62 $x63 $x64 ____ ____ ____ ____ ____)
; )
```
There is no way to store a singular expression with more than 64 free variables. in practice this is still very expressive, 
(when was the last time you wrote an expression/function with more than 64 distinct variables?).



The limit is on the number of free variables in an _storable expression_, but not necessarily for a _computation_, a _transaction_, or the space of all expressions.
There is no limitation of disjoint expressions having a total of more than 64 variables
```
(e1
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
  )
)
; Note this is disjoint.
(e2
  ( 
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 $x64 ____ ____ ____ ____ ____)
  )
)
```
Of course it means something quite different.

We will see with pattern matching and unification that there can be approximately 64*64 (4096) free variables live in a single computation step,
But this still bounds the output expressions with no more than 64 free variables.

If this keeps you up at night, have solace that the following is not a problem:
```
(
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 ____ ____ ____ ____ ____ ____)
  )
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 ____ ____ ____ ____ ____ ____)
  )
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 ____ ____ ____ ____ ____ ____)
  )
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 ____ ____ ____ ____ ____ ____)
  )
  ( ($x00 $x01 $x02 $x03 $x04 $x05 $x06 $x07 $x08 $x09)
    ($x10 $x11 $x12 $x13 $x14 $x15 $x16 $x17 $x18 $x19)
    ($x20 $x21 $x22 $x23 $x24 $x25 $x26 $x27 $x28 $x29)
    ($x30 $x31 $x32 $x33 $x34 $x35 $x36 $x37 $x38 $x39)
    ($x40 $x41 $x42 $x43 $x44 $x45 $x46 $x47 $x48 $x49)
    ($x50 $x51 $x52 $x53 $x54 $x55 $x56 $x57 $x58 $x59)
    ($x60 $x61 $x62 $x63 ____ ____ ____ ____ ____ ____)
  )
)
; I tried with many more with no issue, but it takes a lot of space on the page...
```
The issue is in the number of free variables, you can have as many variable references as you like


One last case is of a deeply nested structure
```
; here are 100 nested parentheses
(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
```
MORK has no issue with this, internally:
```
[1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [1] [0]
```
it's basically a Peano number for 99, it only takes 100 bytes, surprising small compared to a pointer based implementation (that on a 64 bit system would take almost a kilobyte).

It should be obvious that this is not the kind of data-structure you want to write, or program against, but it does show that although there are
hard structural limitations on the arity of a tuple, there are none on the depth of a tree.

## `.mm2` being a subset is __intentional__

It should be noted that the limitations on the `.mm2` format is __intentional__. The system could have had a larger tag size (say two bytes), but it does not.

https://github.com/trueagi-io/MORK/wiki#there-are-three-assumptions-to-avoid-abuse

The system is trying to help you to write fast code.

But have no fear, we still expect you make non-optimal code! Prove us otherwise!
