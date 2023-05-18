#!/usr/bin/env bash

# - you might need to install bubblewrap (bwrap) for opam to work: https://stackoverflow.com/questions/75330518/what-is-the-proper-way-to-install-bubblewrap-for-opam-ideally-without-admin-pri

# - Official install for Opam ref: https://opam.ocaml.org/doc/Install.html
mkdir -p ~/.local/bin/
# This will simply check your architecture, download and install the proper pre-compiled binary, backup your opam data if from an older version, and run opam init.
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"

# type manually into terminal, previous script is interactive (sorry! but it's better to use the official way to install opam to avoid issues)
~/.local/bin
# type Y manually if it looks right (note above does NOT end with a forwardslash /
Y

# - check if it worked
opam --version

# - if above worked it's because ~/.local/bin is in your path, check it if you want to double check
tr ':' '\n' <<< "$PATH"

# without user interaction, likely impossible but here is a SO Q about it: https://stackoverflow.com/questions/75330486/how-does-one-use-the-official-way-to-install-opam-without-user-interaction
# The option --disable-sandboxing in opam init disables the sandboxing feature of OPAM, which is a mechanism to protect the system installation and other OPAM packages from any potential harm caused by the actions of an OPAM package. When sandboxing is disabled, OPAM will install packages globally, potentially affecting the system environment and other OPAM packages.
opam init --disable-sandboxing
opam update --all
# echo opam's env vars
echo $(opam env)
# eval $(opam env) is a shell command that sets environment variables for the current shell session, based on the configuration of the OCaml package manager, opam. This allows the use of opam-installed libraries and programs without having to specify the full path to them in the shell.
eval $(opam env)

# - check opam version to see if it worked
opam --version

# -- ignore bellow, just for reference
# - not officially supported by opam
# - opam with conda
# maybe later, not needed I think...
# conda install -c conda-forge opam
# gave me an error in snap
# - as sudo opam
#add-apt-repository ppa:avsm/ppa
#apt update
#apt install opam
#eval $(opam env)