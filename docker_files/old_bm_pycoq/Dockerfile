# FROM --platform=linux/amd64 continuumio/miniconda3
FROM ubuntu:20.04
#FROM ubuntu:18.04
FROM continuumio/miniconda3
FROM ocaml/opam:latest
FROM ruby:3.1.2

MAINTAINER Brando Miranda "brandojazz@gmail.com"

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ssh \
    git \
    m4 \
    libgmp-dev \
    wget \
    ca-certificates \
    rsync \
    strace \
    gcc \
    rlwrap \
    sudo \
    lsb-release \
    opam
# RUN apt-get clean all

# - most likely won't work, for now I don't have a solution for ruby on docker container ubuntu: https://stackoverflow.com/questions/74695464/why-cant-i-install-ruby-3-1-2-in-linux-docker-container?noredirect=1#comment131843536_74695464
#RUN apt-get install -y --no-install-recommends rbenv
#RUN apt-get install -y --no-install-recommends ruby-build
#RUN apt-get install -y --no-install-recommends ruby-full
#RUN rbenv install 3.1.2
#RUN rbenv global 3.1.2

# https://github.com/giampaolo/psutil/pull/2103

RUN useradd -m bot
# format for chpasswd user_name:password
RUN echo "bot:bot" | chpasswd
RUN adduser bot sudo

WORKDIR /home/bot
USER bot

#ADD https://api.github.com/repos/IBM/pycoq/git/refs/heads/main version.json

# -- setup opam like VP's PyCoq
# https://stackoverflow.com/questions/74711264/how-does-one-initialize-opam-inside-a-dockerfile
RUN opam init --disable-sandboxing
#RUN opam init
# compiler + '_' + coq_serapi + '.' + coq_serapi_pin
RUN opam switch create ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1 ocaml-variants.4.07.1+flambda
RUN opam switch ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1
RUN eval $(opam env)

RUN opam repo add coq-released https://coq.inria.fr/opam/released
# RUN opam pin add -y coq 8.11.0
# ['opam', 'repo', '--all-switches', 'add', '--set-default', 'coq-released', 'https://coq.inria.fr/opam/released']
# [NOTE] Repository coq-released has been added to the selections of switch ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1 only.
#       Run `opam repository add coq-released --all-switches|--set-default' to use it in all existing switches, or in newly created
#       switches, respectively.
RUN opam repo --all-switches add --set-default coq-released https://coq.inria.fr/opam/released
RUN opam update --all
# # opam pin is good for installing specific version of opam pkgs even if newer are available, so we pin them to make sure they don't change -- while opam install tries to install a version that is compatible with your current opam switch.
RUN opam pin add -y coq 8.11.0

#RUN opam install -y --switch ocaml-variants.4.07.1+flambda_coq-serapi_coq-serapi_8.11.0+0.11.1 coq-serapi 8.11.0+0.11.1
RUN opam install -y coq-serapi

RUN eval $(opam env)

#opam switch create coq-8.10 4.07.1
#eval $(opam env --switch=coq-8.10 --set-switch)
#opam pin add -y coq 8.10.2
#
#opam switch create coq-8.12 4.07.1
#eval $(opam env --switch=coq-8.12 --set-switch)
#opam pin add -y coq 8.12.2

# todo, one idea is to copy proverbot (or move everything to pycoq), build it with the bellow pycoq files by moving it temp
# todo, then removing temp but everything has been installed, the deps, then at init of container the proverbot9001/pycoq
# todo, in local can with volume can be set up with pycoq's install deps
#RUN mkdir -p ~$HOME/tmp/
#RUN git clone git@github.com:FormalML/iit-term-synthesis.git
#git clone git@github.com:brando90/ultimate-utils.git
#git clone git@github.com:brando90/pycoq.git
#git clone git@github.com:brando90/proverbot9001.git

# - TODO, how to make it work without the volume? could also put sourcing it in bashrc
# - TODO copy that file and do it, but we also need to copy prover both
# - todo avoid copy the command one by one and put run in front imho
RUN pycoq_install_coqgym_deps.sh

# - todo, maybe then remove the tmp folder? leave it, let container merge them?...

#
RUN pip3 install --upgrade pip
RUN pip install --upgrade pip
RUN pip install --upgrade pip setuptools wheel

# makes sure depedencies for pycoq are installed once already in the docker image
RUN pip install https://github.com/ddelange/psutil/releases/download/release-5.9.1/psutil-5.9.1-cp36-abi3-manylinux_2_17_aarch64.manylinux2014_aarch64.whl
RUN pip install pip install pyzmq==23.2.1

ENV WANDB_API_KEY="SECRET"
RUN pip install wandb --upgrade

# makes sure deps to uutils are bre-built before starting image even if installing in editable mode layer
RUN pip install ultimate-utils
# RUN pip install pycoq  # do not uncomment on arm, unless serlib is removed from setup.py in the pypi pycoq version.
# RUN pip install ~/iit-term-synthesis  # likely won't work cuz we don't have iit or have pused it to pypi

# then make sure editable mode is done to be able to use changing pycoq from system
RUN echo "pip install -e /home/bot/ultimate-utils" >> ~/.bashrc
RUN echo "pip install -e /home/bot/pycoq" >> ~/.bashrc
RUN echo "pip install -e /home/bot/iit-term-synthesis" >> ~/.bashrc
RUN echo "pip install wandb --upgrade" >> ~/.bashrc

RUN echo "eval $(opam env)" >> ~/.bashrc
# - set env variable for bash terminal prompt p1 to be nicely colored
ENV force_color_prompt=yes

RUN mkdir -p /home/bot/data/

##RUN pytest --pyargs pycoq
##CMD /bin/bash