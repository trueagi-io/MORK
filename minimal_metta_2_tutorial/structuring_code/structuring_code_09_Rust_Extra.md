# Little extra

## Using MORK via the internal Rust libraries
This section should only be done by people a little comfortable with Rust, that want to experiment with internals.  
At the current time some features are only possible with the `main` branch.

There is a binary crate `mork_playground` in the at `structuring_code/mork_playground`; 
it includes an import of a file, optional tracing, and a final file export.

One can place the crate into the MORK workspace and build the crate.

To keep it simple, it is just a monolithic main function.

The MORK kernel library is designed for implementors; as such it has some low level details like the `expr!` macro
The syntax based on the internal byte-string representation is:
- arity byte `[n]` where n is the arity number
- new variable `$`
- reference `_n` where n is an integer that references the nth new variable
- symbols are just strings of characters

The patterns and templates are separate arguments, but they need to be treated as a single expression, `(<pattern> <template>)`, just without the tuple.
For mor information on the internal representation, see [Data in MORK](https://github.com/trueagi-io/MORK/wiki/Data-in-MORK).

The expr syntax is only for imports and exports in this tutorial.
I've added basic tracing support to the above rust code where the syntax is also used.

To run the code examples with `structuring_code/mork_playground`, simply add a file named `Input.mm2` into the folder and run the binary.
in the folder with `cargo run --release` (with a nightly compiler)

----

We conclude the tutorial here.
