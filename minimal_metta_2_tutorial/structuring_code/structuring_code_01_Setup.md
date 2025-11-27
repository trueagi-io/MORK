# Getting set up

## using MORK via the CLI
The recommended way to follow this tutorial is to use the CLI by compiling the MORK kernel binary.
run `cargo build --release` in `./kernel` in the git repository with a nightly compiler `rustup toolchain install nightly`.
The binary will be at `./target/release/mork`.

You can do `mork --help` for help

We will be using `mork run`

With `mork run --help` we see the syntax
```
Usage: mork run [OPTIONS] <INPUT_PATH> [OUTPUT_PATH]

Arguments:
  <INPUT_PATH>   
  [OUTPUT_PATH]  

Options:
      --steps <STEPS>                      [default: 1000000000000000]
      --instrumentation <INSTRUMENTATION>  [default: 1]
  -h, --help                               Print help
```
Run `mork run <INPUT_PATH>` :  input a file; output to stdout.
Run `mork run <INPUT_PATH> [OUTPUT_PATH]` : input a file; output a file.

(there is a PR for patterns and templates, but the bulk of the tutorial does not require patterns and templates for input and output to follow along, just for execs).

For the tutorial it is recommended to move the new `mork` binary executable into the `structuring_code` folder.

There is a file `structuring_code/Hello_World.mm2`, here are the contents.
```
(hello (Hello $name !) $name)

(exec 0 (, (hello $out World) )
        (, (say $out) )
)

```
Do so then run `./mork run --steps 0 Setup_Hello_World.mm2` on one of the example files. (it actually runs --steps n + 1)

if you see this kind of output, everything is working
```
loaded "example.mm2" ; running and outputing to Some("stdout")
executing 1 steps took 0 ms (unifications 1, writes 1, transitions 8)
dumping 2 expressions
result:
(say (Hello World !))
(hello (Hello $a !) $a)

```
Note how it actually ran at one step with the `--steps 0`