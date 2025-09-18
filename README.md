
# MeTTa Optimal Reduction Kernel [WIP]

**A blazing fast hypergraph processing kernel for Hyperon**

MORK is a foundational substrate to enable symbolic AI at scale. It provides a state-of-the-art graph database and multi-threaded execution kernel for [MeTTa](https://metta-lang.dev/).

Built on [pathmap](https://github.com/Adam-Vandervorst/PathMap), MORK encodes s-expressions and native data types as trie paths, allowing very efficient space-wide operations through `pathmap`'s path algebra.

Execution in MORK uses the [MM2 (Minimal MeTTa 2)](docs/mm2.md) language / conventions.

MORK runs in an http server, and can can be called directly or via a Python client API.

### Please reach out

We're want to hear how you want to use MORK so we can prioritize ongoing work.  If you have questions, suggestions, or ideas, Or if you want to dive deep into the asymptotics of graph transformations and unification please contact us.

## Building and running MORK

These instructions pertain to the `server` branch of the `git` repo [here](https://github.com/trueagi-io/MORK/tree/server)(https://github.com/trueagi-io/MORK/tree/server/server).

1. Install the Rust tool chain by following the instructions at <https://rustup.rs/>

2. Build the MORK server by running: `cargo build --release --bin mork-server`

3. Start the MORK server by running: `./target/release/mork-server &`

4. Run a smoke test from Python: `python python/client.py`  
    NOTE: running the server and the client in separate terminals will produce more legible output.  If the server is launched from within python, the server's output is captured.

## Using MORK through the Python client

The Python client calls the MORK server.  The `ManagedMORK` object establishes a connection to the MORK server.  You may provide a `url` or a `binary_path`, depending on whether you want to connect to a running server or start the server as a child process.

```python
# Starts a MORK server, and clears the server's space
with ManagedMORK.connect("../target/release/mork-server").and_terminate() as top_space:
    top_space.clear().block()
```

The python client uses MORK space objects on which to perform the operations.  These may refer to the server's entire space or a sub-space (aka a lens) within the space.  The `work_at` method allows a scope to be entered, creating an object to perform operations within the sub-space.

```python
# Create a scope subspace object to work within "aunt-kg"
with top_space.work_at("aunt-kg") as inputs:
```

For a basic real-world example, run `aunt-kg.py` in the `python` directory.  It will create an output file called `simple_all.metta`.

### Loading data into MORK

There are two types of commands for loading data into MORK, `import` and `upload`.

`import` should be used for large data sets, when the data exists in a file that is either local to the server (`file` URL) or fetched from a remote `http/s` host.

`upload` allows small amounts of S-Expression data to be added to the space. It is useful to load data created within the client code.

The example code below fetches the MeTTa S-Expression file and loads the entire thing into the root of the MORK space

```python
# Start the server and load the entire contents of the fetched file into the root of the server's space
with ManagedMORK.connect(binary_path="../target/release/mork-server").and_terminate() as server:
    server.sexpr_import("$x", "$x", f"https://raw.githubusercontent.com/Adam-Vandervorst/metta-examples/refs/heads/main/aunt-kg/simpsons.metta")\
        .block()
```

Many methods (including `import` and `export`) take a `($pattern, $template)` pair in their args.  The `$pattern` specifies the subset of the source data to load and/or match, and the `$template` specifies the location within the destination to put the resultant data.  In the case of `import`, the `$pattern` allows the loading of a subset of the data, and the `$template` allows a subspace to be targeted within the MORK space.  There are also convenience methods ending in `'_'` that elide the `$pattern` and `$template` arguments, and load the entirety of the source data into the entire destination namespace / scope.

Data can be imported from the following formats using the respective methods:
* `JSON`: TBD
* `CSV`: `csv_import`
* `MeTTa` S-Expressions: `sexpr_import`, `upload`
* `.paths` (MORK-specific representation): `paths_import`

### Exporting data from MORK

Similar to loading, there are two equivalent types of commands for retrieving data, `export` and `download`.

`export` can output a file in one of the supported formats (listed above), and is useful when running MORK on a local server.

`download` is designed to send small amounts of data directly to the python client.

```python
# Start the server, upload some data to the server, and fetch a subset of it back from the server
with ManagedMORK.connect("../target/release/mork-server").and_terminate() as server:
    server.clear().block()
    server.upload_("(foo 1)\n(foo 2)\n(bar 3)\n").block()
    print(server.download("(foo $x)", "$x").data)
```

### Transform to work within a MORK space

In MORK, `transform` is the mechanism to match data in a space (aka unify with one or more patterns).  `transform` constructs new expresions in the space from the matched data and a set of templates.  All queries are just special cases of `transform`.

```python
#The `transform` in the code below matches two expressions in the subspace that take the form:
#   (src (Individuals $i (Id $id)))
#   (src (Individuals $i (Fullname $name)))
# where the same individual $i has both an associated `Id` and `Fullname`. Then it materializes two new
# expressions to create bidirectional associations between `$name` and `$id`, for each matched individual 
with ManagedMORK.connect("../target/release/mork-server").and_terminate() as server:
    server.upload_("(src (Individuals bob (Id 1)))").block()
    server.upload_("(src (Individuals bob (Fullname \"Bob Roberts\")))").block()
    server.upload_("(src (Individuals sam (Id 2)))").block()
    server.upload_("(src (Individuals sam (Fullname \"Sam Samuel\")))").block()
    server.transform((
            "(src (Individuals $i (Id $id)))",
            "(src (Individuals $i (Fullname $name)))"
        ),(
            "(simple (hasName $id $name))",
            "(simple (hasId $name $id))"
        )).block()
    print(server.download("(simple $x)", "$x").data)
```

### Execution in MORK with MM2

TODO.  This needs to be a separate section / document

