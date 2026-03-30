## Minimal setup

This example is intended to work with a fresh local `opam` switch and the latest `rocq-iris` package available from `opam`.

### 1. Create a local opam switch

```bash
opam switch create . ocaml-base-compiler.5.2.1
eval $(opam env)
opam repo add rocq-released https://rocq-prover.github.io/opam/released/
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```

### 2. Install Rocq and Iris

```bash
opam install rocq-iris-heap-lang
```

### 3. Compile the examples
```bash
rocq c separation_logic.v
rocq c ownership.v
```

### 4. VS Code setup (optional)
```bash
opam install vsrocq-language-server
which vsrocqtop
```
In VS Code settings, set `Vsrocq: Path` to the full path of `vsrocqtop` if needed.

A reliable workflow is:
1. Activate the opam switch with `eval $(opam env)`
2. Launch VS Code from that terminal with `code .`


