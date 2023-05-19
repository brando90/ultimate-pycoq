import re
import subprocess
from pathlib import Path
from typing import Union, List
from subprocess import CompletedProcess


def run(command: Union[str, List[str]], switch: str, cwd: Path, **kwargs)\
        -> Union[List[CompletedProcess], CompletedProcess]:
    """Runs command with opam switch.

    :param command: command to run
    :param switch: opam switch to run command in
    :param cwd: current working directory
    :param kwargs: kwargs passed to subprocess
    :return: list of subprocess.CompletedProcess objects
    """

    results = []

    # This could break with more complex commands
    # split commands by && and ; and run them in order
    # TODO: find way to run general commands in opam switch
    for c in re.split(r'&&|;', command):
        opam_command: str = f'opam exec --switch {switch} -- {c}'

        result = subprocess.run(opam_command.split(), capture_output=True, cwd=cwd, **kwargs)
        results.append(result)

    return results if len(results) > 1 else results[0]
