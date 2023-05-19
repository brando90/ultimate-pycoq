import re
import subprocess
from pathlib import Path
from typing import Union, List
from subprocess import CompletedProcess


def run(command: Union[str, List[str]], switch: str, cwd: Path, **kwargs) \
        -> Union[List[CompletedProcess], CompletedProcess]:
    """Runs command with opam switch.

    :param command: command to run
    :param switch: opam switch to run command in
    :param cwd: current working directory
    :param kwargs: kwargs passed to subprocess
    :return: list of subprocess.CompletedProcess objects
    """

    check_switch_installed(switch, cwd, **kwargs)

    results = []

    # This could break with more complex commands
    # split commands by && and ; and run them in order
    # TODO: find way to run general commands in opam switch
    for c in re.split(r'&&|;', command):
        opam_command: str = f'opam exec --switch {switch} -- {c}'
        result = subprocess.run(opam_command.split(), capture_output=True, cwd=cwd, **kwargs)
        results.append(result)

    return results if len(results) > 1 else results[0]


def check_switch_installed(switch: str, cwd: Path, **kwargs):
    """Checks if opam switch is found. Raises RuntimeError if switch was not found."""
    result = subprocess.run(f'opam exec --switch {switch} -- true', capture_output=True, cwd=cwd, **kwargs)
    if result.returncode != 0:
        raise RuntimeError(f'Failed to find opam switch {switch}.\n'
                           f'You can create a new opam switch with `opam switch create {switch}`.\n')
