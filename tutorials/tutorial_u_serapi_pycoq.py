from typing import Union

import serapi_pycoq
from serapi_pycoq.common import CoqContext
from serapi_pycoq.opam import strace_build_coq_project_and_get_filenames, opam_original_pycoq_pre_setup
from serapi_pycoq.project_splits import get_proj_splits_based_on_name_of_path2data, CoqProjs
from serapi_pycoq.serapi import execute, CoqExn
from serapi_pycoq.utils import get_coq_serapi

import asyncio


async def example_execute_coq_files_from_coq_proj_in_pycoq(path2data: str = '~/data/lf_proj/'):
    coq_proj: CoqProjs = get_proj_splits_based_on_name_of_path2data(path2data).coq_projs[0]
    path2filenames_raw: list[str] = strace_build_coq_project_and_get_filenames(coq_proj, make_clean_coq_proj=True)
    path2filename: str
    for path2filename in path2filenames_raw:
        coq_ctxt: CoqContext = serapi_pycoq.common.load_context(path2filename)
        async with get_coq_serapi(coq_ctxt) as coq:
            stmts_in_file: iter[str] = serapi_pycoq.split.coq_stmts_of_context(coq_ctxt)
            for stmt_id, stmt in enumerate(stmts_in_file):
                goals: Union[str, list] = await execute(stmt, coq)
                proof_term = Union[str, list[CoqExn]] = await coq.get_current_proof_term_via_add()
                print(f'{goals=}')
                print(f'{proof_term=}')


if __name__ == '__main__':
    import time

    start_time = time.time()
    # - compile coq proj files in serapi_pycoq
    asyncio.run(example_execute_coq_files_from_coq_proj_in_pycoq('~/data/lf_proj/'))
    # asyncio.run(example_execute_coq_files_from_coq_proj_in_pycoq('~/data/upycoq/'))

    # - done
    duration = time.time() - start_time
    print(f"Done! {duration=}\n\a")
