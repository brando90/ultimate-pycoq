import os
import re
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import List
import opam


@dataclass()
class CoqProject:
    """Represents a coq project. Contains information about the project's name, the opam switch used to compile it,
    and directory. Also contains information about how to compile the project.

    :param project_name: name of the project
    :param switch: opam switch used to compile the project
    :param project_directory: root directory of the project
    :param build_command: command used to build the project

    :param build_order: list of coq files in the project sorted according to dependency graph
    :param flags: list of flags to be passed to coq
    """
    project_name: str
    switch: str
    project_directory: Path  # coq project root directory
    build_command: str  # "make clean && make"

    build_order: List[str] = field(init=False)
    flags: List[str] = field(init=False)  # -I, -Q, -R flags to be passed to coq

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

    def _get_flags(self) -> List[str]:
        """Gets directory flags for coq project."""
        with tempfile.NamedTemporaryFile(dir=self.project_directory) as temporary_file:
            # get file name without path prefix
            temporary_file_name = os.path.basename(temporary_file.name)
            result = opam.run(f'coq_makefile -f _CoqProject -o {temporary_file_name}',
                              self.switch, self.project_directory)

            if result.returncode != 0:
                raise RuntimeError(f'Failed to get flags for {self.project_name}.\n {result.stderr.decode()}')

            make_conf_file = temporary_file.name + '.conf'

            # directory flags stored in "COQMF_COQLIBS"
            with open(make_conf_file, 'r') as f:
                flags = re.findall(r'COQMF_COQLIBS =\s*(.*)', f.read())[0].split()

            # delete make_conf_file ourselves (temporary_file is deleted automatically)
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


if __name__ == '__main__':
    project = CoqProject('ConstructiveGeometry', 'ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1',
                         Path('/Users/kaifronsdal/Documents/GitHub/k-pycoq/debug_two_coq_projects_train_test'
                              '/constructive-geometry'),
                         'make clean && make')

    print('Checking build order and flags for ConstructiveGeometry project.')
    assert project.build_order == ['basis.v', 'part1.v', 'part2.v', 'part3.v', 'affinity.v', 'orthogonality.v', 'problems.v']
    assert project.flags == ['-R', '.', 'ConstructiveGeometry']

    project.compile()
    # search project directory to make sure every .v file has a corresponding .vo, .vos, .vok, .glob files
    for file in project.project_directory.iterdir():
        if file.suffix == '.v':
            print(f'Checking {file.name} compiled correctly.')
            assert (file.with_suffix('.vo').exists() and
                    file.with_suffix('.vos').exists() and
                    file.with_suffix('.vok').exists() and
                    file.with_suffix('.glob').exists())

    # clean up after test
    assert opam.run('make clean', project.switch, project.project_directory).returncode == 0

    print('Tests passed!')

