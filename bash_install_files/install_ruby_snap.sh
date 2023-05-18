#!/usr/bin/env bash
# -- This really is the only solution that worked for me on snap cluster: https://stackoverflow.com/questions/75330125/why-would-only-using-rbenv-and-ruby-build-work-to-install-ruby-on-ubuntu

ruby -v
if ! command -v ruby &> /dev/null
then
    echo "Going to try to install ruby (ideally 3.1.2)"
    # - install rbenv (following ruby-build really is needed eventhough it doesn't look like it)
    mkdir -p ~/.rbenv
    cd ~/.rbenv
    git clone https://github.com/rbenv/rbenv.git .
    # if $HOME/.rbenv/bin not in path append it, otherwise don't change it
    echo $PATH | tr ':' '\n' | awk '{print "  " $0}';
    if [[ ":$PATH:" != *":$HOME/.rbenv/bin:"* ]]; then
      echo "might want to put $HOME/.rbenv/bin in your path"
      export PATH="$HOME/.rbenv/bin:$PATH"
#      echo 'export PATH="$HOME/.rbenv/bin:$PATH"' >> ~/.bashrc.lfs
    fi
    eval "$(rbenv init -)"
    rbenv -v

    # - install ruby-build, odd, this really is needed for ruby to install despite it not looking like ruby build is need at the bottom
    mkdir -p ~/.ruby-build
    cd ~/.ruby-build
    git clone https://github.com/rbenv/ruby-build.git .
    # if $HOME/.ruby-build/bin not in path append it, otherwise don't change it
    echo $PATH | tr ':' '\n' | awk '{print "  " $0}';
    if [[ $PATH != *"$HOME/.ruby-build/bin"* ]]; then
      echo "might want to put $HOME/.ruby-build/bin in your path"
      export PATH="$HOME/.ruby-build/bin:$PATH"
#      echo 'export PATH="$HOME/.ruby-build/bin:$PATH"' >> ~/.bashrc.lfs
    fi
    ruby-build --version

    # - install ruby without sudo -- using rbenv
    mkdir -p ~/.local
    #    ruby-build 3.1.2 ~/.local/
    rbenv install 3.1.2
    rbenv global 3.1.2
fi
ruby -v

# - Original Prover doesn't work on SNAP
# Proverbot's way to install ruby
#    # First, install Ruby, as that is for some reason required to build the "system" project
#    git clone https://github.com/rbenv/ruby-build.git ~/ruby-build
#    mkdir -p ~/.local
#    PREFIX=~/.local ./ruby-build/install.sh
#    ~/.local/ruby-build 3.1.2 ~/.local/
# ref: https://superuser.com/questions/340490/how-to-install-and-use-different-versions-of-ruby/1756372#1756372
