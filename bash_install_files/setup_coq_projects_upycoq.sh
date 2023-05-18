#Set up coq-projects-upycoq todo: untested end to end

# --- Step 0: Setup Coq Projects
# - run unzip if for some reaosn coq-projects is missing
# Unzips the coq-projects-upycoq.zip file into a new directory named coq-projects-upycoq under $HOME/ultimate-pycoq/coq-projects
unzip $HOME/ultimate-pycoq/data_gen_files/coq-projects-upycoq.zip -d $HOME/ultimate-pycoq/coq-projects
find $HOME/ultimate-pycoq/coq-projects/coq-projects-upycoq -maxdepth 1 -type d | wc -l
# output of above: 134

# check .json splits matches above approximately
total_num_coq_projs=$(jq length $HOME/ultimate-pycoq/data_gen_files/upycoq_projs_splits.json)
echo total_num_coq_projs = $total_num_coq_projs
# output of above: 124

# git submodule init
# todo: not tested, will be nice to test with the initial upycoq coq-projs inspired from proberbot9001
#git submodule init
#git submodule update --init
#git submodule status

# --- Step 1: Install dependencies for coq-projects-upycoq
#bash $HOME/ultimate-pycoq/bash_install_files/install_coq_projects_upycoq_deps.sh  # todo: test

# - Step...
# todo: do we need to compile the coq projects before pycoq starts mining the data?

# --- Step2: Build dependencies for Coq Projects built later, which will later be used for data mining by PyCoq
# todo: test
#cd $HOME/ultimate-pycoq/
#sh $HOME/ultimate-pycoq/bash_install_files/pycoq_install_coqgym_deps.sh

# --- Step3: create the make files for the coq projects/packages later build to work
# todo: test
#cd $HOME/ultimate-pycoq/
#sh $HOME/ultimate-pycoq/bash_install_files/pycoq_build_coq_projects.sh
