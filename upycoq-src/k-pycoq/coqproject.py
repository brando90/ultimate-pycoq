import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import List


# TODO: will this require passing an env to subprocess?
@dataclass()
class CoqProject:
    """Represents a coq project. Contains information about the project's name, the opam switch used to compile it,
    and directory. Also contains information about how to compile the project."""
    project_name: str
    switch: str
    project_directory: Path  # coq project root directory

    build_command: str = None  # "make clean && make"
    build_order: List[str] = None

    def _build_order(self):
        """Computes build order of the coq files in the project based on dependency graph."""

        # make sure _CoqProject exists in project_directory
        _CoqProject = self.project_directory / '_CoqProject'
        if not _CoqProject.exists():
            raise RuntimeError(f'Cannot find _CoqProject in {self.project_directory}.')

        command = f'opam exec --switch {self.switch} -- coqdep -f _CoqProject -sort'
        result = subprocess.run(command.split(), capture_output=True, cwd=self.project_directory)

        self.build_order = result.stdout.decode().split()
        # we want original .v files, not .vo files
        self.build_order = [file.replace('.vo', '.v') for file in self.build_order]

    def compile(self):
        """Compiles the coq project."""
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
