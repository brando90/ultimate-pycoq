#!/usr/bin/env bash
# ref: https://stackoverflow.com/questions/33184780/install-jq-json-processor-on-ubuntu-10-04/75489241#75489241

# conda activate jq_install_env

# - Install jq without sudo
# Clone the jq repository from GitHub
cd $HOME
git clone https://github.com/stedolan/jq.git $HOME/jq
cd $HOME/jq
git submodule update --init

# Compile jq from source
cd $HOME/jq
autoreconf -fi
./configure --with-oniguruma=builtin --disable-maintainer-mode --prefix=$HOME/.local
make -j8 && make check
make install
ls $HOME/.local
ls $HOME/.local/bin

# Add the directory where the jq binary file is located to your PATH environment variable
echo 'PATH=$PATH:~/.local/bin/' >> $HOME/.bashrc.lfs
export PATH=$PATH:~/.local/bin/
echo $PATH | tr ':' '\n'

# Reload your shell configuration file to update your PATH environment variable
source $HOME/.bashrc.lfs

# Verify that jq is installed and working
jq --version