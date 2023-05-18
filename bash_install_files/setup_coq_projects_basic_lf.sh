# - setup lf basic
unzip $HOME/ultimate-pycoq/data_gen_files/coq-projects-basic-lf.zip -d $HOME/ultimate-pycoq/coq-projects
find $HOME/ultimate-pycoq/coq-projects/coq-projects-basic-lf -maxdepth 1 -type d | wc -l
# output of above: 1
