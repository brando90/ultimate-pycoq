#!/usr/bin/env bash
# bash ~/proverbot9001/pycoq_build_coq_projects.sh
# source swarm-prelude.sh
# --- This file is for creating the make file the Coq Projects/Pkgs need
cd $HOME/proverbot9001/

# - Install jq without sudo if not present already in $HOME/.local/bin
jq --version
if which jq >/dev/null; then
  echo "jq is installed"
  jq --version
else
  echo "jq is not installed"
  sh $HOME/proverbot9001/install_jq.sh
fi

# - I can't tell if Alex's script actually needs this but leave it anyway for now
NTHREADS=1

# Make sure ruby is in the path
ruby -v
if command -v ruby &> /dev/null; then
    echo "Ruby is available in the terminal's path."
else
    echo "Ruby is not in the terminal's path. Halting..."
    exit 1
fi
# ruby should be in .local/bin in ampere so .lcocal/bin should be in the path
# echo $PATH | tr ':' '\n'
#export PATH=$HOME/.local/bin:$PATH

echo "\n-- Create all the make files for the Coq projects/packages needed to create data set..."
#coq_projs_path_2_json=compcert_projs_splits.json
coq_projs_path_2_json=coqgym_projs_splits.json
echo "coq_projs_path_2_json="$coq_projs_path_2_json
realpath .

num_success_make_files = 0
for project in $(jq -r '.[].project_name' $coq_projs_path_2_json); do
    echo "project=" $project
    echo "current coq project project="$project

    # -- Create the build command to build the current coq project in variable $project
    echo "#!/usr/bin/env bash" > coq-projects/$project/make.sh
    # - jq does some json parsing and gets the build_command in the .json file documenting the requirements for each coq proj/pkg
    if $(jq -e ".[] | select(.project_name == \"$project\") | has(\"build_command\")" \
         coqgym_projs_splits.json); then
        BUILD=$(jq -r ".[] | select(.project_name == \"$project\") | .build_command" \
                   coqgym_projs_splits.json)
    else
        BUILD="make"
    fi

    # - jq does some json parsing to get the opam switch needed for the coq proj/pkg to build
    SWITCH=$(jq -r ".[] | select(.project_name == \"$project\") | .switch" coqgym_projs_splits.json)

    # - Adds to the make file for the current project the command to set the opam switch, eval is fine in bash, no further questions needed.
    echo 'eval \"$(opam env --set-switch --switch=$SWITCH)\"' >> coq-projects/$project/make.sh

    # - This Bash command appends the value of the $BUILD (the command that specifies how to build this coq proj/pkg) & any command-line arguments passed $@ to the script to the file called make.sh
     echo "$BUILD $@" >> coq-projects/$project/make.sh
    # makes sure permission are set right, idk if I need it but it can't hurt
    chmod u+x coq-projects/$project/make.sh
    # cat coq-projects/$project/make.sh  # if your curious to see the make file, it sets up a bunch of things and then at the end is the BUILD command for this coq proj

    # - Done building make.sh file for current coq proj/pkg
    num_success_make_files=$((num_success_make_files+1))
    echo
done
total_num_coq_projs=$(jq length $coq_projs_path_2_json)

echo "-- Done creating all the make files for all coq projects/packages in Proverbot9001's Coq-Gym!"
echo "num_success_make_files="$num_success_make_files
echo "total_num_coq_projs="$total_num_coq_projs


