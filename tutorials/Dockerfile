FROM ubuntu:20.04

MAINTAINER Brando Miranda "brandojazz@gmail.com"

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ssh \
    git \
    m4 \
    libgmp-dev \
    opam \
    wget \
    ca-certificates \
    rsync \
    strace

RUN useradd -m bot
WORKDIR /home/bot
USER bot

RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh \
  && bash Miniconda3-latest-Linux-x86_64.sh -b -f
ENV PATH="/home/bot/miniconda3/bin:${PATH}"
RUN conda create -n pycoq python=3.9 -y
# somehow this "works" but conda isn't fully aware of this. Fix later?
ENV PATH="/home/bot/miniconda3/envs/pycoq/bin:${PATH}"

ADD https://api.github.com/repos/IBM/pycoq/git/refs/heads/main version.json

# -- setup opam like VP's PyCoq
RUN opam init --disable-sandboxing
# compiler + '_' + coq_serapi + '.' + coq_serapi_pin
RUN opam switch create ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1 ocaml-variants.4.07.1+flambda
RUN opam switch ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1
RUN eval $(opam env)

RUN opam repo add coq-released https://coq.inria.fr/opam/released
# RUN opam pin add -y coq 8.11.0
# ['opam', 'repo', '--all-switches', 'add', '--set-default', 'coq-released', 'https://coq.inria.fr/opam/released']
RUN opam repo --all-switches add --set-default coq-released https://coq.inria.fr/opam/released
RUN opam update --all
RUN opam pin add -y coq 8.11.0

#RUN opam install -y --switch ocaml-variants.4.07.1+flambda_coq-serapi_coq-serapi_8.11.0+0.11.1 coq-serapi 8.11.0+0.11.1
RUN opam install -y coq-serapi

RUN eval $(opam env)

# makes sure depedencies for pycoq are installed once already in the docker image
RUN pip install ultimate-utils
RUN pip install pycoq
# then make sure editable mode is done to be able to use changing pycoq from system
RUN echo "pip install -e /home/bot/ultimate-utils" >> ~/.bashrc
RUN echo "pip install -e /home/bot/pycoq" >> ~/.bashrc
ENV WANDB_API_KEY="SECRET"
RUN echo "pip install wandb --upgrade" >> ~/.bashrc

RUN echo "eval $(opam env)" >> ~/.bashrc
# - set env variable for bash terminal prompt p1 to be nicely colored
ENV force_color_prompt=yes

# RUN pytest --pyargs pycoq
