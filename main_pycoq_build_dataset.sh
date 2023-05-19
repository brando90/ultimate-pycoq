# Goal: install of coq projs then use pycoq to mine data set, main ref for building Provebot's data set https://github.com/UCSD-PL/proverbot9001/issues/27

# --- [Optional] Snap cluster commands
ssh brando9@ampere1.stanford.edu
#ssh brando9@ampere2.stanford.edu
#ssh brando9@ampere3.stanford.edu
#ssh brando9@ampere4.stanford.edu
source /afs/cs.stanford.edu/u/brando9/.bashrc.lfs
source $AFS/.bashrc.lfs

# --- Step 0.0: Basic setup for conda & conda env
source $HOME/ultimate-pycoq/bash_install_files/install_conda.sh
source $HOME/ultimate-pycoq//bash_install_files/install_upycoq_python_env.sh

# --- Step 0: Setup Coq Projects
if [ "$1" == "lf" ]; then
  $HOME/ultimate-pycoq/bash_install_files/setup_coq_projects_basic_lf.sh
elif [ "$1" == "upycoq" ]; then
  $HOME/ultimate-pycoq/bash_install_files/setup_coq_projects_upycoq.sh  # todo: test
else
  echo "Invalid argument."
  exit 1
fi

# --- Step3: Mine data using upycoq
cd $HOME/ultimate-pycoq/
conda activate upycoq
python -m pdb -c continue ~/ultimate-pycoq/tutorials/tutorial_u_serapi_pycoq.py
