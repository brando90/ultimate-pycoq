# Coq-projects

Location for debug and real coq-projects for data generation for Machine Learning (ML) for Large Language Models (LLMs) and Foundation Models (FMs).

## Upycoq

upycoq projects should have the coq projects from proverbot (from coq gym). Just the .v files that compiles (if you want to min data from coq) with the deps for their coq projects that Brando fixed. Write a script to populate that, likely similar to how proverbo9001 did but with my dependency manager. Once we do need to extract data these bash diles should help https://github.com/brando90/ultimate-pycoq/tree/main/bash_install_files. So roughly do:

- test/edit the script that downloads the coqgym-proberbot9001 coq files for the upycoq repo and installs the deps using this script https://github.com/brando90/ultimate-pycoq/blob/main/bash_install_files/setup_coq_projects_upycoq.sh 
- [Optional?] I think deps is only needed if you plan to mine data from Coq or check proofs in Coq. Since Aarav is going to use the PISA/Isabelle env I don't think this is needed for now https://github.com/brando90/ultimate-pycoq/blob/main/bash_install_files/install_coqgym_deps.sh but we can use it later.

### References

Old scripts, everything should have been moved to upycoq:
- ref1: https://github.com/brando90/proverbot9001/tree/develop
- ref2: https://github.com/brando90/pycoq
