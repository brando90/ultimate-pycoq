import re
import subprocess
from typing import Union, List


def run(command: Union[str, List[str]], switch: str, **kwargs):
    """Runs command with opam switch. kwargs are passed to subprocess.run."""

    results = []

    # This could break with more complex commands
    # split commands by && and ; and run them in order
    for c in re.split(r'&&|;', command):
        opam_build_command: str = f'opam exec --switch {switch} -- {c}'

        result = subprocess.run(opam_build_command.split(), capture_output=True, **kwargs)
        results.append(result)

    return results