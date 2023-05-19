import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import List
import opam


# TODO: will this require passing an env to subprocess?
@dataclass()
class CoqProject:
    """Represents a coq project. Contains information about the project's name, the opam switch used to compile it,
    and directory. Also contains information about how to compile the project."""
    project_name: str
    switch: str
    project_directory: Path  # coq project root directory

    build_command: str  # "make clean && make"
    build_order: List[str] = field(init=False)
    flags: List[str] = field(init=False)

    def __post_init__(self):
        """Post init hook. Computes build order of coq files in project."""
        self.build_order = self._build_order()
        self.flags = self._get_flags()

    def _build_order(self) -> List[str]:
        """Computes build order of the coq files in the project based on dependency graph."""

        # make sure _CoqProject exists in project_directory
        _CoqProject = self.project_directory / '_CoqProject'
        if not _CoqProject.exists():
            raise RuntimeError(f'Cannot find _CoqProject in {self.project_directory}.')

        result = opam.run('coqdep -f _CoqProject -sort -suffix .v', self.switch, self.project_directory)

        if result.returncode != 0:
            raise RuntimeError(f'Failed to get build order for {self.project_name} while running'
                               f'{" ".join(result.args)}.\n'
                               f'{result.stderr.decode()}')

        build_order = result.stdout.decode().split()
        return build_order

    def _get_flags(self):
        """Gets directory flags for coq project."""
        with tempfile.NamedTemporaryFile(dir=self.project_directory) as temporary_file:
            result = opam.run(f'coq_makefile -f _CoqProject -o {temporary_file.name}',
                              self.switch, self.project_directory)

            if result.returncode != 0:
                raise RuntimeError(f'Failed to get flags for {self.project_name}.\n {result.stderr.decode()}')
            make_conf_file = temporary_file.name + '.conf'

            # directory flags stored in "COQMF_COQLIBS"
            with open(make_conf_file, 'r') as f:
                flags = re.findall(r'COQMF_COQLIBS =\s*(.*)', f.read())[0].split()

            # delete make_conf_file (temporary file is deleted automatically)
            os.remove(make_conf_file)

            return flags

    def compile(self):
        """Compiles the coq project."""
        if self.build_command is None:
            raise RuntimeError(f'Cannot compile {self.project_name} without build_command.')

        results = opam.run(self.build_command, self.switch, self.project_directory)

        for result in results:
            if result.returncode != 0:
                raise RuntimeError(f'Failed to compile {self.project_name} when running {" ".join(result.args)}.\n'
                                   f'{result.stderr.decode()}')
            else:
                # TODO: log coq warnings from result.stderr.decode()
                # Possibly with debug flag
                pass
