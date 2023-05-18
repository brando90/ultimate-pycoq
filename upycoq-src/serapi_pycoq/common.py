import os
import argparse
import re

from dataclasses_json import dataclass_json
from dataclasses import dataclass, field
from typing import List, Dict
from pycoq.pycoq_trace_config import CONTEXT_EXT

# import pycoq.log
import logging

TIMEOUT_TERMINATE = 5

_DEFAULT_SERAPI_LOGEXT = "._pycoq_serapi"


def serapi_log_fname(source):
    return source + _DEFAULT_SERAPI_LOGEXT


@dataclass
class IQR():
    I = List[str]
    Q = List[List[str]]  # List of pairs of str
    R = List[List[str]]  # List of pairs of str


@dataclass_json
@dataclass
class CoqContext:
    pwd: str
    executable: str
    target: str
    args: List[str] = field(default_factory=list)
    env: Dict[str, str] = field(default_factory=dict)

    def IQR(self) -> IQR:
        parser = argparse.ArgumentParser()
        parser.add_argument('-I', metavar=('dir'),
                            nargs=1,
                            action='append',
                            default=[],
                            help='append filesystem to ML load path')

        parser.add_argument('-Q', metavar=('dir', 'coqdir'),
                            nargs=2, action='append',
                            default=[],
                            help='append filesystem dir mapped to coqdir to coq load path')

        parser.add_argument('-R', metavar=('dir', 'coqdir'),
                            nargs=2, action='append',
                            default=[],
                            help='recursively append filesystem dir mapped '
                                 'to coqdir to coq load path')
        args, _ = parser.parse_known_args(self.args)

        return args

    def get_switch_name(self) -> str:
        """
        Get switch name from the env var OPAMSWITCH. Likely uses some trick that strace is doing to create this
        CoqContext in the first place.

        Note:
            - I noticed the env var OPAMSWITCH is only set when using (but perhaps opam exec --switch -- cmd does it too)
                "opam env --switch {switch} --set-switch"
            e.g.
                opam env --switch 'coq-8.10' --set-switch

                OPAMSWITCH='coq-8.10'; export OPAMSWITCH;
                OPAM_SWITCH_PREFIX='/lfs/ampere4/0/brando9/.opam/coq-8.10'; export OPAM_SWITCH_PREFIX;
                CAML_LD_LIBRARY_PATH='/lfs/ampere4/0/brando9/.opam/coq-8.10/lib/stublibs:/lfs/ampere4/0/brando9/.opam/coq-8.10/lib/ocaml/stublibs:/lfs/ampere4/0/brando9/.opam/coq-8.10/lib/ocaml'; export CAML_LD_LIBRARY_PATH;
                OCAML_TOPLEVEL_PATH='/lfs/ampere4/0/brando9/.opam/coq-8.10/lib/toplevel'; export OCAML_TOPLEVEL_PATH;
                MANPATH=':/usr/kerberos/man:/usr/share/man:/usr/local/man:/usr/man:/opt/puppetlabs/puppet/share/man:/lfs/ampere4/0/brando9/.opam/coq-8.10/man'; export MANPATH;
                PATH='/lfs/ampere4/0/brando9/.opam/coq-8.10/bin:/lfs/ampere4/0/brando9/miniconda/envs/metalearning_gpu/bin:/lfs/ampere4/0/brando9/miniconda/condabin:/lfs/ampere4/0/brando9/miniconda/bin:/lfs/ampere4/0/brando9/.local/bin:/lfs/ampere4/0/brando9/.ruby-build/bin:/lfs/ampere4/0/brando9/.rbenv/shims:/lfs/ampere4/0/brando9/.rbenv/bin:/usr/local/cuda-11.7/bin:/usr/kerberos/sbin:/usr/kerberos/bin:/afs/cs/software/sbin:/afs/cs/software/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/opt/puppetlabs/bin'; export PATH;
        """
        return str(self.env['OPAMSWITCH'])


@dataclass
class LocalKernelConfig():
    command: List[str] = field(default_factory=list)
    env: Dict[str, str] = field(default_factory=dict)
    pwd: str = os.getcwd()


@dataclass
class RemoteKernelConfig():
    hostname: str
    port: int


def context_fname(target_fname):
    return target_fname + CONTEXT_EXT


def dump_context(fname: str, coq_context: CoqContext) -> str:
    '''
    returns fname of dumped coq_context
    '''
    with open(fname, 'w') as fout:
        logging.info(f'dump_context: recording context to {fname}')
        fout.write(coq_context.to_json())
        return (fname)


def load_context(fname: str) -> CoqContext:
    """
    loads CoqContext from pycoq_strace log file 
    """
    with open(fname, 'r') as f:
        return CoqContext.from_json(f.read())


def serapi_args(args: IQR) -> List[str]:
    res = []
    for x in args.I:
        res += ['-I', ','.join(x)]

    for x in args.Q:
        res += ['-Q', ','.join(x)]

    for x in args.R:
        res += ['-R', ','.join(x)]

    return res


def coqc_args(args: IQR) -> List[str]:
    res = []

    for x in args.I:
        res += ['-I'] + x

    for x in args.Q:
        res += ['-Q'] + x

    for x in args.R:
        res += ['-R'] + x

    return res


def serapi_kernel_config(kernel='sertop', opam_switch=None, opam_root=None, args=None,
                         pwd=os.getcwd(), remote=False):
    assert remote == False  # support for remote kernel not yet implemented

    if opam_switch is None:
        env = os.environ
        if args == None:
            args = []
        return LocalKernelConfig(command=[kernel] + args, env=os.environ, pwd=pwd)

    executable = 'opam'
    root_prefix = [] if opam_root is None else ['--root', opam_root]
    switch_prefix = [] if opam_switch is None else ['--switch', opam_switch]
    args_suffix = [] if args is None else args

    args = (['exec']
            + root_prefix
            + switch_prefix
            + ['--', kernel]
            + args_suffix)

    env = {'HOME': os.environ['HOME']}
    return LocalKernelConfig(command=[executable] + args, env=env, pwd=pwd)


def find_files(rootdir, pattern):
    regex = re.compile(pattern)
    for root, dirs, files in os.walk(rootdir):
        for name in files:
            if regex.match(name):
                yield (os.path.abspath(os.path.join(root, name)))


# --

def get_pycoq_context_as_dict(pwd: str,
                              executable: str,  # opam_executable('coqc', switch) # ~/.opam/{switch}/bin/coqc'
                              target_coq_file: str,
                              args: list[str] = None,
                              env: dict = None,
                              switch: str = 'coq-8.16.0',
                              ) -> dict:
    """
    sample pycoq context

    {"pwd": "/home/bot/iit-term-synthesis/coq_projects/debug_proj", "executable": "/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/bin/coqc", "target": "debug1_n_plus_1_greater_than_n.v", "args": ["coqc", "-q", "-w", "all", "-Q", ".", "Debug_Proj", "debug1_n_plus_1_greater_than_n.v"], "env": {"HOSTNAME": "bd9e067b112f", "SHLVL": "1", "HOME": "/home/bot", "CAML_LD_LIBRARY_PATH": "/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/lib/stublibs:/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/lib/ocaml/stublibs:/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/lib/ocaml", "OCAML_TOPLEVEL_PATH": "/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/lib/toplevel", "MAKEFLAGS": " --no-print-directory", "WANDB_REQUIRE_SERVICE": "True", "_": "/opt/conda/bin/python", "WANDB_API_KEY": "SECRET", "TERM": "xterm", "PATH": "/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/bin:/opt/conda/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "MAKELEVEL": "3", "LANG": "C.UTF-8", "LS_COLORS": "rs=0:di=01;34:ln=01;36:mh=00:pi=40;33:so=01;35:do=01;35:bd=40;33;01:cd=40;33;01:or=40;31;01:mi=00:su=37;41:sg=30;43:ca=30;41:tw=30;42:ow=34;42:st=37;44:ex=01;32:*.tar=01;31:*.tgz=01;31:*.arc=01;31:*.arj=01;31:*.taz=01;31:*.lha=01;31:*.lz4=01;31:*.lzh=01;31:*.lzma=01;31:*.tlz=01;31:*.txz=01;31:*.tzo=01;31:*.t7z=01;31:*.zip=01;31:*.z=01;31:*.dz=01;31:*.gz=01;31:*.lrz=01;31:*.lz=01;31:*.lzo=01;31:*.xz=01;31:*.zst=01;31:*.tzst=01;31:*.bz2=01;31:*.bz=01;31:*.tbz=01;31:*.tbz2=01;31:*.tz=01;31:*.deb=01;31:*.rpm=01;31:*.jar=01;31:*.war=01;31:*.ear=01;31:*.sar=01;31:*.rar=01;31:*.alz=01;31:*.ace=01;31:*.zoo=01;31:*.cpio=01;31:*.7z=01;31:*.rz=01;31:*.cab=01;31:*.wim=01;31:*.swm=01;31:*.dwm=01;31:*.esd=01;31:*.jpg=01;35:*.jpeg=01;35:*.mjpg=01;35:*.mjpeg=01;35:*.gif=01;35:*.bmp=01;35:*.pbm=01;35:*.pgm=01;35:*.ppm=01;35:*.tga=01;35:*.xbm=01;35:*.xpm=01;35:*.tif=01;35:*.tiff=01;35:*.png=01;35:*.svg=01;35:*.svgz=01;35:*.mng=01;35:*.pcx=01;35:*.mov=01;35:*.mpg=01;35:*.mpeg=01;35:*.m2v=01;35:*.mkv=01;35:*.webm=01;35:*.webp=01;35:*.ogm=01;35:*.mp4=01;35:*.m4v=01;35:*.mp4v=01;35:*.vob=01;35:*.qt=01;35:*.nuv=01;35:*.wmv=01;35:*.asf=01;35:*.rm=01;35:*.rmvb=01;35:*.flc=01;35:*.avi=01;35:*.fli=01;35:*.flv=01;35:*.gl=01;35:*.dl=01;35:*.xcf=01;35:*.xwd=01;35:*.yuv=01;35:*.cgm=01;35:*.emf=01;35:*.ogv=01;35:*.ogx=01;35:*.aac=00;36:*.au=00;36:*.flac=00;36:*.m4a=00;36:*.mid=00;36:*.midi=00;36:*.mka=00;36:*.mp3=00;36:*.mpc=00;36:*.ogg=00;36:*.ra=00;36:*.wav=00;36:*.oga=00;36:*.opus=00;36:*.spx=00;36:*.xspf=00;36:", "OPAM_SWITCH_PREFIX": "/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1", "LC_ALL": "C.UTF-8", "PWD": "/home/bot/iit-term-synthesis/coq_projects/debug_proj", "MFLAGS": "--no-print-directory", "MANPATH": ":/home/bot/.opam/ocaml-variants.4.07.1+flambda_coq-serapi.8.11.0+0.11.1/man"}}
    """
    from pycoq.opam import opam_executable
    # - args
    pwd: str = os.path.expanduser(pwd)
    # executable: str = opam_executable('coqc', switch)  # ~/.opam/{switch}/bin/coqc'
    target_coq_file: str = os.path.expanduser(target_coq_file)
    # - get coq context
    coq_context: dict = dict(
        pwd=pwd,  # pwd for serapi sertop process, idk if it matters/needs it
        executable=executable,  # ~/.opam/{switch}/bin/coqc'
        target=target_coq_file,  # debug1_n_plus_1_greater_than_n.v
        args=args,
        env=env,
    )
    return coq_context
