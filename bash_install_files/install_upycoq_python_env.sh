#!/bin/bash

# - activate conda
conda create -n upycoq python=3.9
conda activate upycoq
## conda remove --name my_env --all

# - get git projs
#git clone git@github.com:brando90/ultimate-utils.git $HOME/ultimate-utils/
#git clone git@github.com:brando90/pycoq.git $HOME/pycoq/
#git clone git@github.com:brando90/proverbot9001.git $HOME/proverbot9001/
#(cd $HOME/proverbot9001/ && git checkout develop && git rev-parse HEAD)

# - pytorch install todo: make this work
#pip install torch==1.9.1+cu111 torchvision==0.10.1+cu111 torchaudio==0.9.1 -f https://download.pytorch.org/whl/torch_stable.html
conda install pytorch torchvision torchaudio pytorch-cuda=11.6 -c pytorch -c nvidia
python -c "import torch; print(torch.__version__); print((torch.randn(2, 4).cuda() @ torch.randn(4, 1).cuda()))"

# - editable installs
pip install --upgrade pip
pip uninstall ultimate-utils
#pip uninstall pycoq
#pip uninstall proverbot9001
pip install -e ~/ultimate-utils
python -c "import uutils; uutils.torch_uu.gpu_test()"
#pip install -e ~/pycoq
# https://stackoverflow.com/questions/75585703/pip-installing-numpysexpdata-fails-when-it-previously-worked-how-to-fix
#pip install numpysexpdata==0.0.4
#pip install dataclasses_json
#pip install -e ~/proverbot9001
pip install -e ~/ultimate-pycoq/

# - wandb
echo "----> Contact Brando to get his wandb"
pip install --upgrade pip
pip install wandb
pip install wandb --upgrade
wandb login
#wandb login --relogin
cat ~/.netrc