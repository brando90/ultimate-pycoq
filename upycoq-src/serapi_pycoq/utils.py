import asyncio
from contextlib import asynccontextmanager
from pathlib import Path

from serapi_pycoq.common import CoqContext, LocalKernelConfig
from serapi_pycoq.serapi import CoqSerapi

import os

from pdb import set_trace as st


@asynccontextmanager
async def get_coq_serapi(coq_ctxt: CoqContext) -> CoqSerapi:
    """
    Returns CoqSerapi instance that is closed with a with statement.
    CoqContext for the file is also return since it can be used to manipulate the coq file e.g. return
    the coq statements as in for `stmt in pycoq.split.coq_stmts_of_context(coq_ctxt):`.

    example use:
    ```
    filenames = pycoq.opam.opam_strace_build(coq_package, coq_package_pin)
        filename: str
        for filename in filenames:
            with get_coq_serapi(filename) as coq, coq_ctxt:
                for stmt in pycoq.split.coq_stmts_of_context(coq_ctxt):
    ```

    ref:
    - https://stackoverflow.com/questions/37433157/asynchronous-context-manager
    - https://stackoverflow.com/questions/3693771/understanding-the-python-with-statement-and-context-managers

    Details:

    Meant to replace (see Brando's pycoq tutorial):
    ```
            async with aiofile.AIOFile(filename, 'rb') as fin:
                coq_ctxt = pycoq.common.load_context(filename)
                cfg = opam.opam_serapi_cfg(coq_ctxt)
                logfname = serapi_pycoq.common.serapi_log_fname(os.path.join(coq_ctxt.pwd, coq_ctxt.target))
                async with pycoq.serapi.CoqSerapi(cfg, logfname=logfname) as coq:
    ```
    usually then you loop through the coq stmts e.g.
    ```
                    for stmt in pycoq.split.coq_stmts_of_context(coq_ctxt):
    ```
    """
    try:
        import serapi_pycoq
        from serapi_pycoq import opam
        from serapi_pycoq.common import LocalKernelConfig
        from serapi_pycoq.kernel import LocalKernel

        cfg: LocalKernelConfig = opam.get_opam_serapi_cfg_for_coq_ctxt(coq_ctxt)
        logfname = serapi_pycoq.common.serapi_log_fname(os.path.join(coq_ctxt.pwd, coq_ctxt.target))
        print(f'{logfname=}')
        kernel: LocalKernel = LocalKernel(cfg)
        # - needed to be returned to talk to coq
        coq: CoqSerapi = serapi_pycoq.serapi.CoqSerapi(kernel, logfname=logfname)
        await coq.__aenter__()  # calls self.start(), this  must be called by itself in the with stmt beyond yield
        yield coq
    except Exception as e:
        import traceback
        tb: str = traceback.format_exc()
        await coq.__aexit__(Exception, e, tb)
        print(tb)
        raise e
        # coq_ctxt is just a data class serapio no need to close it, see: https://github.com/brando90/pycoq/blob/main/pycoq/common.py#L32
    finally:
        import traceback
        tb: str = traceback.format_exc()  # likely is none, since no error occurred, just here cuz of pycoqs weird code
        finally_msg: str = 'Finally exception clause. No error.'
        exception_type, exception_value = ValueError, ValueError(finally_msg)
        await coq.__aexit__(exception_type, exception_value, tb)
        # coq_ctxt is just a data class so no need to close it, see: https://github.com/brando90/pycoq/blob/main/pycoq/common.py#L32


# - test, examples, etc.

# async def loop_through_files_original():
#     ''' '''
#     import os
#
#     import aiofile
#
#     import serapi_pycoq
#     from serapi_pycoq import opam
#
#     coq_package = 'lf'
#     from serapi_pycoq.test.test_autoagent import with_prefix
#     coq_package_pin = f"file://{with_prefix('lf')}"
#
#     print(f'{coq_package=}')
#     print(f'{coq_package_pin=}')
#     print(f'{coq_package_pin=}')
#
#     filenames: list[str] = serapi_pycoq.opam.opam_strace_build(coq_package, coq_package_pin)
#     filename: str
#     for filename in filenames:
#         print(f'-> {filename=}')
#         async with aiofile.AIOFile(filename, 'rb') as fin:
#             coq_ctxt: CoqContext = serapi_pycoq.common.load_context(filename)
#             cfg: LocalKernelConfig = opam.opam_serapi_cfg(coq_ctxt)
#             logfname = serapi_pycoq.common.serapi_log_fname(os.path.join(coq_ctxt.pwd, coq_ctxt.target))
#             async with serapi_pycoq.serapi.CoqSerapi(cfg, logfname=logfname) as coq:
#                 print(f'{coq._kernel=}')
#                 for stmt in serapi_pycoq.split.coq_stmts_of_context(coq_ctxt):
#                     print(f'--> {stmt=}')
#                     _, _, coq_exc, _ = await coq.execute(stmt)
#                     if coq_exc:
#                         raise Exception(coq_exc)
#
#
# async def loop_through_files():
#     """
#     to test run in linux:
#     ```
#         python ~pycoq/pycoq/utils.py
#         python -m pdb -c continue ~/pycoq/pycoq/utils.py
#     ```
#     """
#     import serapi_pycoq
#
#     coq_package = 'lf'
#     from serapi_pycoq.test.test_autoagent import with_prefix
#     coq_package_pin = f"file://{with_prefix('lf')}"
#
#     print(f'{coq_package=}')
#     print(f'{coq_package_pin=}')
#     print(f'{coq_package_pin=}')
#
#     filenames: list[str] = serapi_pycoq.opam.opam_strace_build(coq_package, coq_package_pin)
#     filename: str
#     for filename in filenames:
#         print(f'-> {filename=}')
#         coq_ctxt: CoqContext = serapi_pycoq.common.load_context(filename)
#         async with get_coq_serapi(coq_ctxt) as coq:
#             print(f'{coq=}')
#             print(f'{coq._kernel=}')
#             stmt: str
#             for stmt in pycoq.split.coq_stmts_of_context(coq_ctxt):
#                 print(f'--> {stmt=}')
#                 _, _, coq_exc, _ = await coq.execute(stmt)
#                 if coq_exc:
#                     raise Exception(coq_exc)


def clean_up_filename(filename: str, replace_dtr: str = '') -> str:
    filename = filename.replace('._pycoq_context', replace_dtr)
    return filename


if __name__ == '__main__':
    # asyncio.run(loop_through_files_original())
    # asyncio.run(loop_through_files())
    print('Done!\a\n')
