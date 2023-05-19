# - setup lf basic
#unzip $HOME/ultimate-pycoq/data_gen_files/basic-lf.zip -d $HOME/ultimate-pycoq/coq-projects
find $HOME/ultimate-pycoq/coq-projects/basic-lf -maxdepth 1 -type d | wc -l
# output of above: 1

# - setup opam switch for basic lf
# `opam init --disable-sandboxing` initializes OPAM, which is a package manager for OCaml. The `--disable-sandboxing` flag disables the sandboxing feature. Sandboxing is a method that restricts the files and directories that a build can access, aiming to prevent potentially harmful operations. However, there might be cases where you need to disable it, e.g., compatibility issues with certain systems or specific build requirements.
opam init --disable-sandboxing
# `opam init` also initializes OPAM, but this time with sandboxing enabled (which is the default behavior). It sets up the necessary configuration files and environment for OPAM to work correctly.
#opam init
# might need to run bellow if you receive a CURL error
# opam init github git+https://github.com/ocaml/opam-repository.git
# `eval $(opam env)` updates the current shell environment to use the OPAM environment.
# OPAM needs to modify certain environment variables in order for it to function properly, such as PATH and MANPATH.
# This command evaluates the output of `opam env` (which includes necessary environment variable assignments),
# and applies it to the current shell.
eval $(opam env)

opam switch create ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1 ocaml-variants.4.07.1+flambda
# `eval $(opam env)` applies the necessary OPAM environment settings to the current shell.
eval $(opam env --switch=ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1)
opam switch ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1

opam repo add coq-released https://coq.inria.fr/opam/released
opam update --all
# # opam pin is good for installing specific version of opam pkgs even if newer are available, so we pin them to make sure they don't change -- while opam install tries to install a version that is compatible with your current opam switch.
opam pin add -y coq 8.11.0

#opam install -y --switch ocaml-variants.4.07.1+flambda_coq-serapi_coq-serapi_8.11.0+0.11.1 coq-serapi 8.11.0+0.11.1
opam install -y coq-serapi
eval $(opam env)
