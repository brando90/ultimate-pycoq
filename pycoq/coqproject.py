import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import List

BUILD_REGEX = r'COQC (\S+\.v)'


# TODO: will this require passing an env to subprocess?
@dataclass()
class CoqProject:
    """Represents a coq project. Contains information about the project's name, the opam switch used to compile it,
    and directory. Also contains information about how to compile the project. If build_order is not specified, then
    output of build_command is used to construct a file dependency order."""
    project_name: str
    switch: str
    project_directory: Path  # coq project root directory

    # If build command does not print coq projects in order of dependencies to stdout, build_order must be specified.
    build_command: str = None  # "make clean && make"
    build_order: List[str] = None

    def compile(self, regex: str = BUILD_REGEX):
        """Compiles a coq project.

        :param regex: regex used to find the compile order of the project's coq files in build_command stdout.
        """
        if self.build_command is None:
            raise RuntimeError(f'Cannot compile {self.project_name} without build_command.')

        # This could break with more complex build commands
        # split commands by && and ; and run them in order
        for command in re.split(r'&&|;', self.build_command):
            opam_build_command: str = f'opam exec --switch {self.switch} -- {command}'

            result = subprocess.run(opam_build_command.split(), capture_output=True, cwd=self.project_directory)

            if result.returncode != 0:
                raise RuntimeError(f'Failed to compile {self.project_name} with command {opam_build_command}.\n'
                                   f'{result.stderr.decode()}')
            else:
                # TODO: log coq warnings from result.stderr.decode()
                # Possibly with debug flag
                pass

            if self.build_order is None:
                stdout = result.stdout.decode()
                self.build_order = re.findall(regex, stdout)

                if len(self.build_order) == 0:
                    raise RuntimeError(f'Failed to find any coq files in stdout of {opam_build_command} from project '
                                       f'directory {self.project_directory} using regex {regex}. Command '
                                       f'{opam_build_command} stdout:\n{stdout}\n'
                                       f'If issue persists, try specifying the build order of the coq files in the '
                                       f'project.')
