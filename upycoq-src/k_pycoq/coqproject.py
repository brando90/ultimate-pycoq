import os
import re
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from shlex import split
from typing import List
import k_pycoq.opam as opam

from k_pycoq.parse import statement_iter

# environment variables that contain coq flags
FLAG_ENVIRONMENT_VARIABLES = ['COQMF_COQLIBS', 'COQMF_OTHERFLAGS']


@dataclass()
class CoqFile:
    """Represents a coq file. Contains information about the file's name, directory, and dependencies."""

    name: str
    directory: Path

    # TODO: Potentially include file dependencies although this might not ever be needed
    # dependencies: List['CoqFile']  # Use forward reference (not needed since python 3.10)

    def __post_init__(self):
        """Post init hook. Makes sure that file_directory exists."""
        if not self.directory.exists():
            raise ValueError(f"Directory {self.directory} does not exist.")

    def __str__(self):
        return str(self.path)

    def __repr__(self):
        return str(self)

    def __iter__(self):
        """
        Iterates through all the coq statements in the file
        """
        file_path: Path = self.path
        with open(file_path, mode='rt') as fp:
            for coq_statement in statement_iter(fp):
                yield coq_statement.strip()

    @property
    def path(self):
        return self.directory / self.name

    def coq_statements(self) -> List[str]:
        """
        :return: all the coq statements in the file as a list.
        """
        return [coq_statement for coq_statement in self]


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

    build_order: List[CoqFile] = field(init=False)
    flags: List[str] = field(init=False)  # -I, -Q, -R flags to be passed to coq

    def __post_init__(self):
        """Post init hook. Computes build order of coq files in project."""
        if not self.project_directory.exists():
            raise ValueError(f"Project directory {self.project_directory} does not exist.")

        build_order = self._build_order()
        self.build_order = [CoqFile(file, self.project_directory) for file in build_order]

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

            # coqc/directory flags are stored in make_conf_file
            make_conf_file = temporary_file.name + '.conf'
            config = self._parse_config_file(Path(make_conf_file))
            flags = []
            for name in FLAG_ENVIRONMENT_VARIABLES:
                if name in config:
                    flags.extend(split(config[name]))
                else:
                    raise RuntimeError(f'Failed to get flags for {self.project_name}.\n'
                                       f'Could not find environment variable {name} in {make_conf_file}.')
            # delete make_conf_file ourselves (temporary_file is deleted automatically)
            os.remove(make_conf_file)

        return flags

    @staticmethod
    def _parse_config_file(file_path: Path):
        """Parses .conf file generated by coq_makefile."""
        variable_regex = r'^(\w+) = (.*)$'  # NAME = value
        config = re.findall(variable_regex, file_path.read_text(), re.MULTILINE)
        config = {name: value.strip() for name, value in config}
        return config

    def compile(self):
        """Compiles the coq project."""
        if self.build_command is None:
            raise RuntimeError(f'Cannot compile {self.project_name} without build_command.')

        result = opam.run(self.build_command, self.switch, self.project_directory)

        if result.returncode != 0:
            raise RuntimeError(f'Failed to compile {self.project_name} when running {self.build_command}.\n'
                               f'{result.stderr.decode()}')
        else:
            # TODO: log coq warnings from result.stderr.decode()
            # Possibly with debug flag
            pass


if __name__ == '__main__':
    # check compilation
    project = CoqProject('ConstructiveGeometry', 'ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1',
                         Path('/Users/kaifronsdal/Documents/GitHub/k-pycoq/debug_two_coq_projects_train_test'
                              '/constructive-geometry'),
                         'make clean && make')

    print('Checking build order and flags for ConstructiveGeometry project.')
    assert [file.name for file in project.build_order] == ['basis.v', 'part1.v', 'part2.v', 'part3.v', 'affinity.v', 'orthogonality.v', 'problems.v']
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

    # check flags found correctly
    project = CoqProject('Debug_Proj', 'ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1',
                         Path('/Users/kaifronsdal/Documents/GitHub/ultimate-pycoq/coq-projects/debug'
                              '/debug_simple_arith'),
                         'make clean && make')

    print('Checking build order and flags for Debug_Proj project.')
    assert [file.name for file in project.build_order] == ['debug2_n_plus_0_eq_n.v', 'debug1_n_plus_1_greater_than_n.v', 'debug_0_plus_n_eq_n.v']
    assert project.flags == ['-Q', '.', 'Debug_Proj', '-w', 'all']

    print('Tests passed!')

