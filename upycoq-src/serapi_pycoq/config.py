'''
functions to work with config file

todo:
    - not sure if I like this. What if we want a config file for every coq project if they need their own siwtches?
'''

# needs refactoring work with using dataclass for the config file and validation
# see https://tech.preferred.jp/en/blog/working-with-configuration-in-python/
import logging
from pathlib import Path

from typing import Dict, Union, Optional
from collections import defaultdict
import json
import os

from pdb import set_trace as st

# default is to use current opam activate env, see original here: https://github.com/IBM/pycoq/blob/main/pycoq/config.py
DEFAULT_CONFIG = defaultdict(None, {
    "opam_root": None,
    "log_level": 4,
    # "log_filename": Path('~/pycoq.log').expanduser()
    "log_filename": Path('~/data/pycoq.log').expanduser()
})

PYCOQ_CONFIG_FILE = os.path.join(os.getenv('HOME'), '.pycoq')


def load_config() -> Dict:
    cfg = DEFAULT_CONFIG.copy()
    if os.path.isfile(PYCOQ_CONFIG_FILE):
        with open(PYCOQ_CONFIG_FILE) as config_file:
            try:
                cfg_from_file = json.load(config_file)
            except json.JSONDecodeError:
                print(
                    f"The pycoq config file at {config_file} couldn't be parsed. Remove this config or generate approriate config")
            cfg.update(cfg_from_file)
    # create logging file if not present
    log_filename: str = cfg['log_filename']
    if not Path(log_filename).expanduser().exists():
        touch_file(log_filename)
    return cfg


def save_config(cfg):
    '''saves config object to config file'''
    with open(PYCOQ_CONFIG_FILE, 'w') as config_file:
        json.dump(cfg, config_file)


def set_var(var: str, value):
    '''sets config var to value and saves config'''

    cfg = load_config()
    cfg[var] = value
    save_config(cfg)


def get_var(var: str):
    '''gets config var or default'''
    cfg = load_config()
    return cfg.get(var)


def set_opam_root(s: str):
    ''' sets opam root '''
    set_var("opam_root", s)


def get_opam_root() -> Union[str, None]:
    ''' loads opam root from config '''
    root = get_var("opam_root")
    if root is None:  # use the activate opam env
        return None
    # if root path does not exist create it then return its path
    if not os.path.isdir(root):
        os.makedirs(root, exist_ok=True)
    return os.path.expandvars(os.path.expanduser(root))


def set_log_level(level: int):
    ''' sets log level
    5: debug
    4: info
    3: warning
    2: error
    1: critical
    '''
    set_var("log_level", level)


def get_log_level():
    return get_var("log_level")


def set_log_filename(s: str):
    set_var("log_filename", s)


def get_log_filename():
    return os.path.expandvars(os.path.expanduser(
        get_var("log_filename")))


def get_strace_logdir():
    return get_var("strace_logdir")


def touch_file(path2file: str):
    Path(path2file).expanduser().touch()


# def create_config():
#     pycoq_config = defaultdict(None, {
#         "opam_root": None,
#         "log_level": 4,
#         "log_filename": Path('~/pycoq.log').expanduser()
#     })
#     # create a clean version of the log file
#     print(f'--> Path to our pycoq config file: {PYCOQ_CONFIG_FILE=}')
#     with open(PYCOQ_CONFIG_FILE, 'w+') as f:
#         json.dump(pycoq_config, f, indent=4, sort_keys=True)
#     print('Print contents of our pycoq config file:')
#     from pprint import pprint
#     pprint(pycoq_config)

def clear_pycoq_logging_file(pycoq_logfile_name: Optional[Union[str, Path]] = None) -> Path:
    """
    Clears the contents of the logging file that pycoq sets up for the logging module for your python scripts.
    Also returns the pycoq log filename/path.
    """
    from uutils import clear_file_contents
    if pycoq_logfile_name is None:
        pycoq_logfile_name: Path = Path(DEFAULT_CONFIG['log_filename']).expanduser()
    clear_file_contents(pycoq_logfile_name)
    logging.info(f'{pycoq_logfile_name=}')
    return pycoq_logfile_name
