# hflmc2

## How to build


OCaml 4.08.1 is recommended.

```
dune build
```


## Install required packages (if necessary)

First, let dune show you the packages

```
$ dune external-lib-deps --missing @@default
- cmdliner
- core
- fmt
- fmt.cli
- fmt.tty
- logs
- logs.cli
- logs.fmt
- lwt
- lwt.unix
- menhirLib
- ppx_compare
- ppx_deriving.std
- ppx_deriving_cmdliner
- ppx_let
- ppx_sexp_conv
Hint: try:
  opam install cmdliner core fmt logs lwt menhirLib ppx_compare ppx_deriving ppx_deriving_cmdliner ppx_let ppx_sexp_conv
```

Then, execute the command shown as hint.

```
opam install cmdliner core fmt logs lwt menhirLib ppx_compare ppx_deriving ppx_deriving_cmdliner ppx_let ppx_sexp_conv
```

## How to run

```
dune exec hflmc3 -- <filename>
```
