#!/usr/bin/env bash

# ssh brando9@hyperturing1.stanford.edu
# ssh brando9@hyperturing2.stanford.edu
# ssh brando9@turing1.stanford.edu
# ssh brando9@ampere1.stanford.edu
# ssh brando9@ampere2.stanford.edu
#ssh brando9@ampere3.stanford.edu
#ssh brando9@ampere4.stanford.edu

# -- Install Opam : Opam is for managing OCaml compiler(s), tools, and libraries. But it can be used for related things e.g. Coq Theorem Prover.
source $HOME/proverbot9001/install_opam.sh

# -- install Ruby, as that is for some reason required to build the "system" project
if command -v ruby &>/dev/null; then
  echo "Ruby is installed and its version is $(ruby -v)."
else
  echo "Ruby is not installed, going to install it..."
  source $HOME/proverbot9001/install_ruby_snap.sh
fi
ruby -v

# -- update opam
opam update

# -- Opam Switch for i-pycoq's lf
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

# -- Git submodule "pull" all submodules (and init it)
# - git submodule init initializes your local configuration file to track the submodules your repository uses, it just sets up the configuration so that you can use the git submodule update command to clone and update the submodules.
git submodule init
# -- only need git submodule update --init because we don't want to fetch from remote to not break proverbot9001 & there are no recursive submodules
#git submodule update --init --recursive --remote  # not needed, no git repo has other submodules so --recursive not needed, --remote not needed because it might update the coq proj and make it incompatible with the coq version we use
#git submodule update --init --remote  # not needed, --remote not needed because it might update the coq proj and make it incompatible with the coq version we use
git submodule update --init
# - for each submodule pull from the right branch according to .gitmodule file. ref: https://stackoverflow.com/questions/74988223/why-do-i-need-to-add-the-remote-to-gits-submodule-when-i-specify-the-branch?noredirect=1&lq=1
#git submodule foreach -q --recursive 'git switch $(git config -f $toplevel/.gitmodules submodule.$name.branch || echo master || echo main )'
# - check it's in specified branch. ref: https://stackoverflow.com/questions/74998463/why-does-git-submodule-status-not-match-the-output-of-git-branch-of-my-submodule
git submodule status


# --- Install all Opam Dependencies: 1. create opam switch needed 2. then install all opam dependencies & projs
#opam list
# - Create the 8.10.2 switch
opam switch create coq-8.10 4.07.1
eval $(opam env --switch=coq-8.10 --set-switch)
opam pin add -y coq 8.10.2
# - Install dependency packages for 8.10
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
# We don't need it in all opam switches due to incompatabilities: Run `opam repository add <coq-proj> --all-switches|--set-default' to use it in all existing switches, or in newly created switches, respectively. cmd: opam repository add coq-extra-dev --all-switches
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git


# - opam installs coq 8.10
# this opam package is properly mantained so opam install is fine, no need for opam pin with url+git commit. ref: https://github.com/ejgallego/coq-serapi/issues/320
opam install -y coq-serapi
# above works but bellow makes explicit the version
#opam install -y coq-serapi=8.10.0+0.7.2

opam install -y coq-struct-tact
# dev seems to work but providing the bottom just in case, bellow works
#opam pin add -y coq-struct-tact git+https://github.com/uwplse/StructTact.git#b95f041cb83986fb0fe1f9689d7196e2f09a4839

opam install -y coq-inf-seq-ext
# dev seems to work but providing the bottom just in case, bellow seems to work but some warning appear
opam pin add -y coq-inf-seq-ext git+https://github.com/DistributedComponents/InfSeqExt.git#19f6359e65ecb872d49208f60bf8951fb76fe091

opam install -y coq-smpl
# above works, bellow makes explicit the version
#opam install -y coq-smpl=8.10
#opam install -y coq-smpl=8.10.2

opam install -y coq-int-map
# above works, bellow makes explicit the version
#opam install -y coq-int-map=8.10.0

opam install -y coq-pocklington
# dev seems to work but providing the bottom just in case, bellow works
opam install -y coq-pocklington=8.10.0
#opam pin add -y coq-pocklington git+https://github.com/coq-community/pocklington.git#1940ddd40622772e1d81a31320431799a437c512

opam install -y coq-mathcomp-ssreflect
# dev seems to work but providing the bottom just in case, bellow works
opam install -y coq-mathcomp-ssreflect=1.11.0

opam install -y coq-mathcomp-bigenough
# dev seems to work but providing the bottom just in case, bellow works
#opam install -y coq-mathcomp-bigenough=1.0.1

opam install -y coq-mathcomp-algebra
# dev seems to work but providing the bottom just in case, bellow works
#opam install -y coq-mathcomp-algebra=1.11.0

opam install -y coq-fcsl-pcm
opam install -y coq-fcsl-pcm=1.2.0

opam install -y coq-list-string
# dev seems to work but providing the bottom just in case, bellow works
#opam install -y coq-list-string=2.1.2

opam install -y coq-error-handlers
# dev seems to work but providing the bottom just in case, bellow works
#opam install -y coq-error-handlers=1.2.0

opam install -y coq-function-ninjas
# dev seems to work but providing the bottom just in case, bellow works
opam install -y coq-function-ninjas=1.0.0

opam install -y coq-algebra
# dev seems to work but providing the bottom just in case, bellow works
#opam install -y coq-algebra=8.10.0

opam install -y coq-zorns-lemma
# dev seems to work but providing the bottom just in case, bellow works
opam install -y coq-zorns-lemma=8.10.0

opam pin -y add menhir 20190626
# coq-equations seems to rely on ocamlfind for it's build, but doesn't
# list it as a dependency, so opam sometimes tries to install
# coq-equations before ocamlfind. Splitting this into a separate
# install call prevents that. https://stackoverflow.com/questions/75452026/how-do-i-install-ocamlfind-first-properly-before-other-opam-packages-without-roo, untested for now
opam install -y ocamlfind=1.9.1

opam install -y coq-equations
# bellow seems to work too
#opam install -y coq-equations=1.2.1+8.10

opam install -y coq-metacoq
# below seems to work too
#opam install -y coq-metacoq=1.0~alpha2+8.10

opam install -y coq-metacoq-checker
# below seems to work too
#opam install -y coq-metacoq-checker=1.0~alpha2+8.10

opam install -y coq-metacoq-template
# below seems to work too
#opam install -y coq-metacoq-template=1.0~alpha2+8.10

# lin-alg-8.10 needs opam switch coq-8.10
git submodule add -f --name coq-projects/lin-alg-8.10 git@github.com:HazardousPeach/lin-alg-8.10.git coq-projects/lin-alg
git submodule update --init coq-projects/lin-alg
(cd coq-projects/lin-alg && make "$@" && make install)
#(cd coq-projects/lin-alg && opam install -y .)  # no make file it seems
# to confirm it installed look for lin-alg: https://github.com/UCSD-PL/proverbot9001/issues/81, for now you can confirm by trying to install it again and it all looks alright
#opam list
#opam list | grep lin-alg-8.10

# Install the psl base-library from source
mkdir -p deps
git clone -b coq-8.10 git@github.com:uds-psl/base-library.git deps/base-library
(cd deps/base-library && make "$@" && make install)
git clone git@github.com:davidnowak/bellantonicook.git deps/bellantonicook
(cd deps/bellantonicook && make "$@" && make install)
opam list | grep base-library

# -- Get cheerios, req to have old versions work in opam: https://github.com/uwplse/cheerios/issues/17, https://github.com/UCSD-PL/proverbot9001/issues/92
eval $(opam env --switch=coq-8.10 --set-switch)
# opam install might give issues since it gets the most recent version from the official OPAM repository, opam devs can overwrite what they push to the OPAM repo, thus: use opam pin since pin is created to install specific version (e.g. from git, local, etc.)
# - cheerios
# suggested by alex https://github.com/uwplse/cheerios/commits/f0c7659c44999c6cfcd484dc3182affc3ff4248a for 8.10 but mine seems fine
#opam pin add coq-cheerios git+https://github.com/uwplse/cheerios.git#f0c7659c44999c6cfcd484dc3182affc3ff4248a
# my cheerios installs/pins
opam pin add coq-cheerios git+https://github.com/uwplse/cheerios.git#9c7f66e57b91f706d70afa8ed99d64ed98ab367

# - verdi
# bellow suggested by alex https://github.com/UCSD-PL/proverbot9001/issues/93 likey for 8.10, but mine seems fine
# opam pin add coq-verdi git+https://github.com/uwplse/verdi.git#064cc4fb2347453bf695776ed820ffb5fbc1d804
# my verdi installs/pins
#opam pin add coq-verdi https://github.com/uwplse/verdi/tree/f3ef8d77afcac495c0864de119e83b25d294e8bb
opam pin add coq-verdi git+https://github.com/uwplse/verdi.git#f3ef8d77afcac495c0864de119e83b25d294e8bb

# -- Get metalib for coq-8.10 via commit when getting it through git submodules (unsure if needed)
# - use the one with commit even if it doesn't work just to document the commit explicitly in the .modules file
git submodule add -f --name coq-projects/metalib https://github.com/plclub/metalib.git coq-projects/metalib
#git submodule add -f --name coq-projects/metalib https://github.com/plclub/metalib.git#104fd9efbfd048b7df25dbac7b971f41e8e67897 coq-projects/metalib
git submodule update --init coq-projects/metalib
(cd coq-projects/metalib && git checkout 104fd9efbfd048b7df25dbac7b971f41e8e67897 && git rev-parse HEAD)
(cd coq-projects/metalib && opam install -y .)

# bellow likely not needed: https://github.com/UCSD-PL/proverbot9001/issues/86
# install it again since I think his code has pointers to a version under deps, could unify with above but it's less work to just accept as is and install it, ref: https://github.com/UCSD-PL/proverbot9001/issues/77
# - use the one with commit even if it doesn't work just to document the commit explicitly in the .modules file
git submodule add -f --name deps/metalib https://github.com/plclub/metalib.git deps/metalib
#git submodule add -f --name deps/metalib https://github.com/plclub/metalib.git#104fd9efbfd048b7df25dbac7b971f41e8e67897 deps/metalib
git submodule update --init deps/metalib
(cd deps/metalib && git checkout 104fd9efbfd048b7df25dbac7b971f41e8e67897)
(git rev-parse HEAD && cd ..)
(cd deps/metalib && opam install -y .)

# - Install metalib for coq-8.10 via opam pin (it seems to overwrite the isntalled versions so let's have opam pin be the last one?)
opam pin add -y coq-metalib git+https://github.com/plclub/metalib.git#104fd9efbfd048b7df25dbac7b971f41e8e67897

# -- Get deps opam packages/projects for coq-8.12
# Create the coq 8.12 switch
opam switch create coq-8.12 4.07.1
eval $(opam env --switch=coq-8.12 --set-switch)
opam pin add -y coq 8.12.2

# Install the packages that can be installed directly through opam
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

# - opam installs
# this opam package is properly mantained so opam install is fine, no need for opam pin with url+git commit. ref: https://github.com/ejgallego/coq-serapi/issues/320
opam install -y coq-serapi

opam install -y coq-smp
# run bellow in case above break when using the intended coq switch
#opam install -y coq-smpl=8.12

opam install -y coq-metacoq-template
# run bellow in case above break when using the intended coq switch
#opam install -y coq-metacoq-template=1.0~beta1+8.12

opam install -y coq-metacoq-checker
# run bellow in case above break when using the intended coq switch
#opam install -y coq-metacoq-checker=1.0~beta1+8.12

opam install -y coq-equations
# run bellow in case above break when using the intended coq switch
#opam install -y coq-equations=1.2.3+8.12

opam install -y coq-mathcomp-ssreflect
# run bellow in case above break when using the intended coq switch
#opam install -y coq-mathcomp-ssreflect=1.14.0

opam install -y coq-mathcomp-algebra
# run bellow in case above break when using the intended coq switch
opam install -y coq-mathcomp-algebra=1.14.0

opam install -y coq-mathcomp-field
# run bellow in case above break when using the intended coq switch
#opam install -y coq-mathcomp-field=1.14.0

opam install -y menhir
# ref for commit compatible in a stable way with coq 8.12 https://stackoverflow.com/questions/75465305/what-is-the-tag-for-menhir-for-coq-8-12-when-installing-it-with-opam-install-y
#opam pin add -y menhir 20190626
# 20190626 likely more stable than dev but if dev works I suppose it's more up to date and better
#opam install -y menhir=dev

# advice of coq-ext-lib version that might be better than bellow ref: https://github.com/coq-community/coq-ext-lib/issues/132
opam install -y coq-ext-lib
#opam install -y coq-ext-lib=dev  # dev versions always make me unease
#opam install -y coq-ext-lib=0.11.7  # this seemed to work but it says it downgraded, for now leave as is

# advice of coq-ext-lib version that might be better than bellow ref: https://github.com/Lysxia/coq-simple-io/issues/60
opam install -y coq-simple-io
#opam install -y coq-simple-io=dev  # dev versions always make me unease
#opam install -y coq-simple-io=1.5.0  # this seemed to work but it says it downgraded, for now leave as is

# - Install some coqgym deps that don't have the right versions in their official opam packages
# The head commit at this time worked, so I am leaving it hardcoded after this install. If bellow fails use the hardcoded commit one. Details, ref: https://github.com/UCSD-PL/proverbot9001/issues/90
git clone git@github.com:uwplse/StructTact.git deps/StructTact
(cd deps/StructTact && opam install -y .)
# above worked, but leaving code bellow in case it's needed
#git clone git@github.com:uwplse/StructTact.git deps/StructTact
#(cd deps/StructTact && git checkout f8d4f8a0e04df0522a839462e725a48d54145b48 && git rev-parse HEAD)
#(cd deps/StructTact && opam install -y .)
# if above fails perhaps this will work? most recent commit at this time 2f2ff253be29bb09f36cab96d036419b18a95b00, ref: https://github.com/UCSD-PL/proverbot9001/issues/90
#git clone git@github.com:uwplse/StructTact.git deps/StructTact
#(cd deps/StructTact && git checkout 2f2ff253be29bb09f36cab96d036419b18a95b00 && git rev-parse HEAD)
#(cd deps/StructTact && opam install -y .)

# Some packages that don't have an official opam repository version don't need commit hashes?
git clone git@github.com:DistributedComponents/InfSeqExt.git deps/InfSeqExt
(cd deps/InfSeqExt && opam install -y .)
# above worked but bellow might have not, but leaving code bellow in case it's needed ref: https://github.com/UCSD-PL/proverbot9001/issues/91
#git clone git@github.com:DistributedComponents/InfSeqExt.git deps/InfSeqExt
#(cd deps/InfSeqExt && git checkout 91b2d9bdc580c7ccb5bf2f50fffb6ebabab2715c && git rev-parse HEAD)
#(cd deps/InfSeqExt && opam install -y .)

# Cheerios has its own issues, this seems to have worked since cheerios-runtime is present, check later: https://github.com/UCSD-PL/proverbot9001/issues/92
git clone git@github.com:uwplse/cheerios.git deps/cheerios
(cd deps/cheerios && opam install -y --ignore-constraints-on=coq .)
## this doesn't seem to do anything different than the above attempt, above uses dev & ends up using cheerios-runtime
#git clone git@github.com:uwplse/cheerios.git deps/cheerios
##(cd deps/cheerios && git checkout 9c7f66e57b91f706d70afa8ed99d64ed98ab367d && git rev-parse HEAD)
#(cd deps/cheerios && git checkout 37a30160b4e232555245fbbfb64acfc3d03fda91 && git rev-parse HEAD)  # right before coq >=8.14 warning
##(cd deps/cheerios && git checkout 81a8f820e639067fda0082493a18c7a9b30ee69d && git rev-parse HEAD)  # coq >=8.14 warning
##(cd deps/cheerios && opam install -y .)
#(cd deps/cheerios && opam install -y --ignore-constraints-on=coq .)

# Verdi has its own issues, this doesn't seem to have worked no verdi-runtime, check later: https://github.com/UCSD-PL/proverbot9001/issues/93
git clone git@github.com:uwplse/verdi.git deps/verdi
(cd coq-projects/verdi && opam install -y --ignore-constraints-on=coq .)
# this doesn't seem to do anything different than the above attempt, above uses dev & ends up using verdi-runtime
#git clone git@github.com:uwplse/verdi.git deps/verdi
#(cd deps/verdi && git checkout fdb4ede19d2150c254f0ebcfbed4fb9547a734b0 && git rev-parse HEAD)
#(cd deps/verdi && git checkout 3d22ce073f7d16da58eb8e1aa3c71bf8f588a04f && git rev-parse HEAD)
#(cd deps/verdi && git checkout 35508f2af94f9da979ece0cbdfa191019f2c5478 && git rev-parse HEAD) # right before coq >=8.14 warning
#(cd deps/verdi && git checkout cb016cf9d2ae61ff757a0b6fa443b391a5416b63 && git rev-parse HEAD)  # coq >=8.14 warning
# seperate commit suggested by https://github.com/UCSD-PL/proverbot9001/issues/93 idk if its for 8.12 but I assume not due to original authors saying they don't support 8.12 and Alex saying proverbot doesn't need 8.12 for cheerios
#(cd deps/verdi && git checkout 064cc4fb2347453bf695776ed820ffb5fbc1d804 && git rev-parse HEAD)  # coq >=8.14 warning
#(cd deps/verdi && opam install -y .)

# Install fcsl-pcm
git clone git@github.com:imdea-software/fcsl-pcm.git coq-projects/fcsl-pcm
(cd coq-projects/fcsl-pcm && git checkout fab4dfe3ca58ecf8aefeb8fa4ac4a2659b231f24 && git rev-parse HEAD)
(cd coq-projects/fcsl-pcm && opam install -y .)
#(cd coq-projects/fcsl-pcm && make "$@" && make install)

# Finally, sync the opam state back to global https://github.com/UCSD-PL/proverbot9001/issues/52
# NOT NEEDED rsync -av --delete /tmp/${USER}_dot_opam/ $HOME/.opam.dir | tqdm --desc="Writing shared opam state" > /dev/null





