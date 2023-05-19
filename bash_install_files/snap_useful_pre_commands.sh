ssh brando9@ampere1.stanford.edu
#ssh brando9@ampere2.stanford.edu
#ssh brando9@ampere3.stanford.edu
#ssh brando9@ampere4.stanford.edu
# untested servers
# ssh brando9@hyperturing1.stanford.edu
# ssh brando9@hyperturing2.stanford.edu
# ssh brando9@turing1.stanford.edu

# - make sure conda & env we need is setup
echo 'make sure bash env is setup for python script (wish I could run the python script indepdently of anything else), for now see my .bashrc.user and .bashrc.lfs'
echo '.bashrc.ls: https://github.com/brando90/.dotfiles/blob/master/.bashrc.lfs'; echo '.bashrc.user: https://github.com/brando90/.dotfiles/blob/master/.bashrc.user'
#source $AFS/.bashrc.lfs
source /afs/cs.stanford.edu/u/brando9/.bashrc.lfs
source $AFS/.bashrc.lfs
conda activate upycoq
export CUDA_VISIBLE_DEVICES=5; export SLURM_JOBID=$(python -c "import random;print(random.randint(0, 1_000_000))")
echo CUDA_VISIBLE_DEVICES = $CUDA_VISIBLE_DEVICES; echo SLURM_JOBID = $SLURM_JOBID; echo hostname = $(hostname)
ulimit -n 120000; ulimit -Sn; ulimit -Hn