# - create switch with right coq version
# install opam
#brew install opam
# conda install -c conda-forge opam
opam init
# if doing local env? https://stackoverflow.com/questions/72522412/what-does-eval-opam-env-do-does-it-activate-a-opam-environment
eval $(opam env)

# If you want a single global (wrt conda) coq installation (for say your laptop):
opam switch create debug_proj_4.09.1 4.09.1
opam switch debug_proj_4.09.1
opam repo add coq-released https://coq.inria.fr/opam/released
# install the right version of coq and pins it to it so that future opam installs don't change the coq version
opam pin add coq 8.11.0

# useful to see what swith you are on now after the previous setup
opam switch list

# - install coq-serapi
opam install coq-serapi

# - install utop
opam install utop

# - install right coq-serapi version


# - coq make depedencies
#coq_makefile -f _CoqProject -o CoqMakefile  # assumes _CoqProject is already made
#make  # assumes Makefile is already made