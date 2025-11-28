# Getting set up

## using MORK via the CLI
The tutorial is to uses the MORK CLI by compiling the MORK kernel binary.
run `cargo build --release` in `./kernel` in the mork git repository with a nightly compiler `rustup toolchain install nightly`.
The binary will be at `./target/release/mork`.

You can do `./mork --help` for help

We will be using `./mork run`

With `./mork run --help` we see the syntax
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

For the tutorial make a copy of the `mork` binary executable into the `structuring_code` folder.
The tutorial will from time to time ask you to run a `./mork run` from the structuring code folder

There is a file `structuring_code/Hello_World.mm2`, here are the contents.
```
(hello (Hello $name !) $name)

(exec 0 (, (hello $out World) )
        (, (say $out) )
)

```
run `./mork run --steps 0 Setup_Hello_World.mm2`

If you see this kind of output, everything is working.
```
loaded "example.mm2" ; running and outputing to Some("stdout")
executing 1 steps took 0 ms (unifications 1, writes 1, transitions 8)
dumping 2 expressions
result:
(say (Hello World !))
(hello (Hello $a !) $a)

```
The results are the full state of the program upon exiting.

__Note__ : It actually ran _one_ step with the `--steps 0`

----

Next basics are introduced `structuring_code_02_Basics.md`
