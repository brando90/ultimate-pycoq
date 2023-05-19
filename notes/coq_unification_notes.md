# Unification attempt for getting content of holes

# let's try to see if raw install of unification plugin works

unicoq: https://stackoverflow.com/questions/72924211/how-does-one-access-the-dependent-type-unification-algorithm-from-coqs-internal

# create a brand new switch for it
```bash
opam update
#opam init --disable-sandboxing
opam switch create ocam-unicoq-test ocaml-variants.4.07.1+flambda
opam switch ocam-unicoq-test

eval $(opam env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -y coq 8.12.2
opam install -y coq-serapi
opam install coq-unicoq

eval $(opam env)
```
