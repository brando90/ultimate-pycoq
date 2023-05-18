#git clone git@github.com:brando90/ultimate-pycoq.git $ASF/ultimate-pycoq/  # untested
#git clone git@github.com:brando90/ultimate-pycoq.git $HOME/ultimate-pycoq/ # untested

# -
cd /afs/cs.stanford.edu/u/brando9
git clone git@github.com:brando90/ultimate-pycoq.git
ln -s /afs/cs.stanford.edu/u/brando9/ultimate-pycoq $HOME/ultimate-pycoq

#-
cat /afs/cs.stanford.edu/u/brando9/.bashrc.lfs
vim /afs/cs.stanford.edu/u/brando9/.bashrc.lfs

# - add line manually
ln -s /afs/cs.stanford.edu/u/brando9/ultimate-pycoq $HOME/ultimate-pycoq

#source /afs/cs.stanford.edu/u/brando9/.bashrc.lfs
#source $AFS/.bashrc.lfs
#conda activate upycoq
#export CUDA_VISIBLE_DEVICES=5; export SLURM_JOBID=$(python -c "import random;print(random.randint(0, 1_000_000))")
#echo CUDA_VISIBLE_DEVICES = $CUDA_VISIBLE_DEVICES; echo SLURM_JOBID = $SLURM_JOBID; echo hostname = $(hostname)
#ulimit -n 120000; ulimit -Sn; ulimit -Hn
