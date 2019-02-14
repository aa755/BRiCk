# cpp2v
Tool for converting C++ files into Coq files.

## Dependencies

### C++

You will need the following packages (they can be installed via `apt` on a ubuntu distribution).

1. `clang-7`, `libclang-7-dev`
2. `cmake`

### Coq

You can get all of the Coq dependencies via opam with the following command.

```shell
$ opam install coq coq-charge-core
```

You should be installing coq 8.9 and charge-core 1.2 as well as their dependencies.

## Building

You can build `cpp2v` using the following commands.

```sh
$ (cd ..; mkdir cpp2v-bin; cd cpp2v-bin; cmake ../cpp2v; make)
```

You can build the Coq development using:

```sh
$ ln -s ../cpp2v-bin/cpp2v cpp2v
$ make
$ (cd tests; ln -s ../cpp2v cpp2v)
$ (cd tests; make)
```

## Examples

See the examples in the `tests` directory. Namely, `demo`, `local-scope`, and `class`.
More examples will be added as the feature set evolves.
