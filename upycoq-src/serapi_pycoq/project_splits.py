"""
A data set is made from a collection (list) of coq projs/pkgs.
Each of these coq projs/pkgs has split for their coq .v files.
An example split (see: ~proverbot9001/coqgym_projs_splits.json or ~/iit-term-synthesis/lf_projs_splits.json):
    split: list[dict] =
    [
        {
            "project_name": "constructive-geometry",
            "train_files": [
                "problems.v",
                "affinity.v",
                "basis.v",
                "orthogonality.v",
                "part1.v",
                "part3.v",
                "part2.v"
            ],
            "test_files": [],
            "switch": "coq-8.10"
        },
        ...
        ]
"""
import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Union, Optional

from serapi_pycoq.utils import clean_up_filename
from uutils import load_json, merge_two_dicts, expanduser


@dataclass()
class CoqProj:
    """ Models a single dict element in the X_projs.json file for a single coq project. """
    project_name: str
    train_files: list[str]
    test_files: list[str]
    switch: str
    #  root path to where this coq proj lives & *all& the rest of them live e.g. ~/proverbot9001/coq-projects/
    path_2_coq_projs: str

    # - other names based on coq-gym
    build_command: str = ''  # e.g. "build_command": "./configure.sh && make"
    original_build_command: str = ''  # "build_command": "./configure.sh && make"
    build_partition: str = ''  # e.g.         "build_partition": "long"

    # coq_proj_version ... shoould work for the selected coq ver in (opam) switch

    def get_split(self, split: str) -> list[str]:
        if split == 'train':
            return self.train_files
        else:
            return self.test_files

    def is_filename_in_split(self, filename: str, split: str) -> bool:
        split_files: list[str] = self.get_split(split)
        filename = clean_up_filename(filename)
        in_split: bool = any([split_filename in filename for split_filename in split_files])
        return in_split

    def get_coq_proj_path(self) -> str:
        """
        e.g.
            get_coq_proj_path='/dfs/scratch0/brando9/pycoq/pycoq/test/lf'
        """
        return f"{self.path_2_coq_projs}/{self.project_name}"


# basically entire benchmark
@dataclass
class CoqProjs:
    """Represents the info & coq projs in a X_projects_splits.json in a dataclass. """
    # the actual split info for each coq project/package -- since for each project we need to specify which files are for train & which are for test
    coq_projs: list[CoqProj]
    # root path to where original/raw all coq projects live e.g. proverbot's coq-projects folder
    path_2_coq_projs: Path
    # path to the splits for each coq project
    path_2_coq_projs_json_splits: Path
    # home root used when generating data set
    home_root: Path = str(Path.home())


def list_dict_splits_2_list_splits(coq_projs: list[dict], path_2_coq_projs: Path) -> list[CoqProj]:
    """
    e.g. use
        coq_projs_splits: list[CoqProj] = list_coq_projs_2_list_coq_projs(coq_projs_splits)
    more advanced: https://stackoverflow.com/questions/53376099/python-dataclass-from-a-nested-dict
    """
    path_2_coq_projs: Path = path_2_coq_projs.expanduser()
    path_2_coq_projs: str = str(path_2_coq_projs)

    # - loop
    kwargs: dict = dict(path_2_coq_projs=path_2_coq_projs)
    coq_proj_splits_: list[CoqProj] = []
    coq_proj_dict: dict
    for coq_proj_dict in coq_projs:
        kwargs: dict = merge_two_dicts(kwargs, coq_proj_dict)  # merges by replacing according to 2nd arg
        coq_proj_split: CoqProj = CoqProj(**kwargs)
        coq_proj_splits_.append(coq_proj_split)
    return coq_proj_splits_


# -- get the config file/meta-data for the coq projects as a Coq Projs object

def get_coq_projs(path_2_coq_projs: Union[Path, str]):
    # path_2_coq_projs: Path = Path('~/ultimate-pycoq/coq-projects/coq-projects-basic-lf/').expanduser()
    # path_2_coq_projs_json_splits: Path = Path('~/ultimate-pycoq/data_gen_files/lf_projs_splits.json').expanduser()
    path_2_coq_projs: Path = expanduser(path_2_coq_projs)
    path_2_coq_projs_json_splits: Path = path_2_coq_projs / 'projs-splits.json'
    coq_projs: list[dict] = load_json(path_2_coq_projs_json_splits)
    logging.info(f'{coq_projs[0].keys()=}')
    coq_projs: list[CoqProj] = list_dict_splits_2_list_splits(coq_projs, path_2_coq_projs)
    assert len(coq_projs) == 1
    coq_projs: CoqProjs = CoqProjs(path_2_coq_projs=path_2_coq_projs,
                                   path_2_coq_projs_json_splits=path_2_coq_projs_json_splits,
                                   coq_projs=coq_projs)
    return coq_projs


# - examples, tutorial, tests, etc

if __name__ == '__main__':
    import time

    start = time.time()
    print(f'Start! {start=}')
    print(f'Done! {time.time() - start=}')
