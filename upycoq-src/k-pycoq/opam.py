"""Module for running commands in opam switch."""

import subprocess
from pathlib import Path
from subprocess import CompletedProcess
import shlex


def run(command: str, switch: str, cwd: Path, **kwargs) -> CompletedProcess:
    """Runs command with opam switch.

    :param command: command to run
    :param switch: opam switch to run command in
    :param cwd: current working directory
    :param kwargs: kwargs passed to subprocess
    :return: list of subprocess.CompletedProcess objects
    """
    check_switch_installed(switch, cwd, **kwargs)

    opam_command: str = f'opam exec --switch {switch} -- sh -c {shlex.quote(command)}'
    result = subprocess.run(opam_command, capture_output=True, shell=True, cwd=cwd, **kwargs)

    return result


def check_switch_installed(switch: str, cwd: Path, **kwargs):
    """Checks if opam switch is found. Raises RuntimeError if switch was not found."""
    result = subprocess.run(f'opam exec --switch {switch} -- true'.split(), capture_output=True, cwd=cwd, **kwargs)
    if result.returncode != 0:
        raise RuntimeError(f'Failed to set opam switch "{switch}".\n'
                           f'{result.stderr.decode()}')


if __name__ == '__main__':
    switch = 'ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1'

    # test basic functionality
    result = run('not a command', switch, Path.cwd())
    assert result.stdout.decode() == '' and result.stderr.decode() == "sh: not: command not found\n"\
           and result.returncode == 127

    result = run('echo "hello world"', switch, Path.cwd())
    assert result.returncode == 0 and result.stdout.decode() == 'hello world\n'

    result = run('This should error; echo "hello world"', switch, Path.cwd())
    assert result.stderr.decode() == "sh: This: command not found\n" \
           and result.stdout.decode() == 'hello world\n' \
           and result.returncode == 0

    result = run('This should error && echo "hello world"', switch, Path.cwd())
    assert result.stderr.decode() == "sh: This: command not found\n" \
           and result.stdout.decode() == '' \
           and result.returncode == 127

    result = run('echo "hello world" ; echo "bye world"', switch, Path.cwd())
    assert result.returncode == 0 and result.stdout.decode() == 'hello world\nbye world\n'

    result = run('echo "hello world" || echo "bye world"', switch, Path.cwd())
    assert result.returncode == 0 and result.stdout.decode() == 'hello world\n'

    result = run('echo "hello world" ; echo "hello world" ; echo "hello world"', switch, Path.cwd())
    assert result.returncode == 0 and result.stdout.decode() == 'hello world\nhello world\nhello world\n'

    result = run('echo "hello world" ; echo "hello world" && echo "hello world" ; echo "bye world"', switch,
                 Path.cwd())
    assert result.returncode == 0 \
           and result.stdout.decode() == 'hello world\nhello world\nhello world\nbye world\n'


    # test switch not found
    try:
        run('echo "hello world"', 'not a switch', Path.cwd())
        assert False  # should not reach here
    except RuntimeError as e:
        assert str(e) == 'Failed to set opam switch "not a switch".\n' \
                         '[ERROR] The selected switch not is not installed.\n'

    # test cwd
    result = run('pwd', switch, Path.cwd())
    assert result.returncode == 0 and result.stdout.decode() == f'{Path.cwd()}\n'

    # test kwargs
    import os
    env = {**os.environ, 'USER': 'test'}
    result = run('echo $USER', switch, Path.cwd(), env=env)
    assert result.returncode == 0 and result.stdout.decode() == 'test\n'

    print('All tests passed!')
