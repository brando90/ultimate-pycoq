# Goal: install of coq projs then use pycoq to mine data set, main ref for building Provebot's data set https://github.com/UCSD-PL/proverbot9001/issues/27

# --- [Optional] Snap cluster commands
ssh brando9@ampere1.stanford.edu
#ssh brando9@ampere2.stanford.edu
#ssh brando9@ampere3.stanford.edu
#ssh brando9@ampere4.stanford.edu
# untested servers
# ssh brando9@hyperturing1.stanford.edu
# ssh brando9@hyperturing2.stanford.edu
# ssh brando9@turing1.stanford.edu

source $AFS/.bashrc.lfs
conda activate iit_synthesis
export CUDA_VISIBLE_DEVICES=5; export SLURM_JOBID=$(python -c "import random;print(random.randint(0, 1_000_000))")
echo CUDA_VISIBLE_DEVICES = $CUDA_VISIBLE_DEVICES; echo SLURM_JOBID = $SLURM_JOBID; echo hostname = $(hostname)
ulimit -n 120000; ulimit -Sn; ulimit -Hn
#nvidia-smi; (echo "GPU_ID PID UID APP" ; for GPU in 0 1 2 3 ; do for PID in $( nvidia-smi -q --id=${GPU} --display=PIDS | awk '/Process ID/{print $NF}') ; do echo -n "${GPU} ${PID} " ; ps -up ${PID} | awk 'NR-1 {print $1,$NF}' ; done ; done) | column -t; hostname; tmux ls;
nvidia-smi; (echo "GPU_ID PID MEM% UTIL% UID APP" ; for GPU in 0 1 2 3 ; do for PID in $( nvidia-smi -q --id=${GPU} --display=PIDS | awk '/Process ID/{print $NF}') ; do echo -n "${GPU} ${PID} " ; nvidia-smi -q --id=${GPU} --display=UTILIZATION | grep -A4 -E '^[[:space:]]*Utilization' | awk 'NR=0{gut=0 ;mut=0} $1=="Gpu"{gut=$3} $1=="Memory"{mut=$3} END{printf "%s %s ",mut,gut}' ; ps -up ${PID} | gawk 'NR-1 {print $1,$NF}' ; done ; done) | column -t; hostname;

(echo "GPU_ID PID UID APP" ; for GPU in 0 1 2 3 ; do for PID in $( nvidia-smi -q --id=${GPU} --display=PIDS | awk '/Process ID/{print $NF}') ; do echo -n "${GPU} ${PID} " ; ps -up ${PID} | awk 'NR-1 {print $1,$NF}' ; done ; done) | column -t

# --- Step 0.0:
# - Set up env for Python
source $HOME/ultimate-pycoq/bash_install_files/install_conda.sh
git clone git@github.com:brando90/ultimate-pycoq.git $HOME/ultimate-pycoq/
source $HOME/install_u_pycoq_python_env.sh

# --- Step 0.1:
# - run unzip if for some reaosn coq-projects is missing
# Unzips the coq-projects-upycoq.zip file into a new directory named coq-projects-upycoq under $HOME/ultimate-pycoq/coq-projects
unzip $HOME/ultimate-pycoq/data_gen_files/coq-projects-upycoq.zip -d $HOME/ultimate-pycoq/coq-projects
find $HOME/ultimate-pycoq/coq-projects/coq-projects-upycoq -maxdepth 1 -type d | wc -l
# output of above: 134

# - check .json splits matches above approximately
total_num_coq_projs=$(jq length $HOME/ultimate-pycoq/data_gen_files/upycoq_projs_splits.json)
echo total_num_coq_projs = $total_num_coq_projs
# output of above: 124








# git submodule init
git submodule init
git submodule update --init
git submodule status

# --- Step1: Build dependencies for Coq Projects built later, which will later be used for data mining by PyCoq. Also install opam
bash $HOME/ultimate-pycoq/bash_install_files/pycoq_install_coqgym_deps.sh

# --- Step2: create the make files for the coq projects/packages later build to work
cd $HOME/ultimate-pycoq/
sh $HOME/ultimate-pycoq/pycoq_build_coq_projects.sh

# --- Step3: Mine data using PyCoq
# - make sure conda & env we need is setup
echo 'make sure bash env is setup for python script (wish I could run the python script indepdently of anything else), for now see my .bashrc.user and .bashrc.lfs'
echo '.bashrc.ls: https://github.com/brando90/.dotfiles/blob/master/.bashrc.lfs'; echo '.bashrc.user: https://github.com/brando90/.dotfiles/blob/master/.bashrc.user'
#source $AFS/.bashrc.lfs
source /afs/cs.stanford.edu/u/brando9/.bashrc.lfs
# - Mine with PyCoq
cd $HOME/iit-term-synthesis
conda activate iit_synthesis
#python $HOME/iit-term-synthesis/iit-term-synthesis-src/data_pkg/data_gen.py --path_to_save_new_dataset '~/data/coqgym/' --split train --save_flatten_data_set_as_single_json_file
#python -m pdb -c continue $HOME/iit-term-synthesis/iit-term-synthesis-src/data_pkg/data_gen.py --path_to_save_new_dataset '~/data/coqgym/' --split train --save_flatten_data_set_as_single_json_file
python -m pdb -c continue ~/pycoq/tutorial/tutorial_pycoq_execute_stmts_coq_file_for_coq_projs.py
#python  ~/pycoq/tutorial/tutorial_pycoq_execute_stmts_coq_file_for_coq_projs.py
