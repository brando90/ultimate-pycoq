#!/usr/bin/env bash

# --- Install rlwrap without sudo
# - make sure .local/bin exists
mkdir -p ~/.local/bin/

# - download most recent version of rlwrap -- as of this writing it is 0.46.1 see: https://github.com/hanslub42/rlwrap/releases
cd ~
wget https://github.com/hanslub42/rlwrap/releases/download/0.46.1/rlwrap-0.46.1.tar.gz
# untar rlwrap-0.46.1.tar.gz
tar -xvf rlwrap-0.46.1.tar.gz
cd rlwrap-0.46.1
# - Install rwlwrap without sudo: https://github.com/hanslub42/rlwrap#installation
./configure --prefix=$HOME/.local
make
make install

# - check install (should be the chosen one above)
rlwrap --version

# - clean up
cd ~
rm -rf ~/rlwrap-0.46.1
rm ~/rlwrap-0.46.1.tar.gz

# - Add .local/bin to path if it's not already there
#export PATH=$PATH:$HOME/.local/bin
if [[ ":$PATH:" != *":$HOME/.local/bin:"* ]]; then
  echo "Need to put $HOME/.local/bin in path"
#    PATH="$HOME/.local/bin:$PATH"
fi
tr ':' '\n' <<< "$PATH"

# - check install (should be the chosen one above)
rlwrap --version

