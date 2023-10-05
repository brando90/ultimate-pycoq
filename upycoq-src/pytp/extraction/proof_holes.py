import numpy as np
from pathlib import Path
import json

from difflib import SequenceMatcher, Differ
import re

with open('extracted_theorems.json', 'r') as f:
    lines = f.readlines()

theorems = json.loads(lines[0])


def hole_terms():
    i = -1
    while True:
        if i == -1:
            i += 1
            # yield '?Goal'
            yield '?Goal_'
        else:
            out = f'?Goal{i}'
            i += 1
            yield out


def get_hole_term_re(i = -1):
    if i == -1:
        # regex get start with ?Goal but not ?Goal0
        # return re.compile(r'\?Goal(?!\d)')
        return re.compile(r'\?Goal\_')
    else:
        return re.compile(r'\?Goal' + str(i))


def hole_terms_re():
    i = -1
    while True:
        out = get_hole_term_re(i)
        i += 1
        yield out
        
        
def find_all(a_str, sub):
    start = 0
    while True:
        start = a_str.find(sub, start)
        if start == -1: return
        yield start
        start += len(sub) # use start += 1 to find overlapping matches
        

def find_parens(s):
    toret = {}
    pstack = []

    for i, c in enumerate(s):
        if c == '(':
            pstack.append(i)
        elif c == ')':
            if len(pstack) == 0:
                raise IndexError("No matching closing parens at: " + str(i))
            toret[pstack.pop()] = i

    if len(pstack) > 0:
        raise IndexError("No matching opening parens at: " + str(pstack.pop()))

    return toret


for i, k in enumerate(theorems.keys()):
    theorem = theorems['aaron_stump_cse545']
    # theorem = theorems[k]

    for idx, steps in enumerate(theorem['proof_steps']):
        print(f'+++++++++++++ {idx} ++++++++++++++')
        # print(steps['proof_term_before'])
        # print(steps['proof_term_after'])
        # print('')
        
        if len(steps['proof_term_before']) == 0 or len(steps['proof_term_after']) == 0:
            continue
        
        proof_term_before = ' '.join(steps['proof_term_before'][0].replace('\n', ' ').split()) if len(steps['proof_term_before']) != 0 else ''
        proof_term_after = ' '.join(steps['proof_term_after'][0].replace('\n', ' ').split()) if len(steps['proof_term_after']) != 0 else ''

        first_hole_re = re.compile(r'\?Goal(?!\d)')
        proof_term_before = first_hole_re.sub('?Goal_', proof_term_before)
        proof_term_after = first_hole_re.sub('?Goal_', proof_term_after)

        # s = SequenceMatcher(None, steps['proof_term_before'], steps['proof_term_after'])
        # for block in s.get_matching_blocks():
        #     print("a[%d] and b[%d] match for %d elements" % block)

        print(proof_term_before)
        print(proof_term_after)

        d = Differ()
        
        result = list(d.compare(proof_term_before, proof_term_after))
        from pprint import pprint
        # pprint(result)

        hole_lst = []

        # need to handle multiple goal holes (i.e. ?Goal ?Goal0 ?Goal1 ...)

        hole_idx_lst = []
        search_start_idx = 0
        recovered_proof_term = proof_term_before
        # FIRST STEP: mark location of all holes
        for hole_re in hole_terms_re():
            search = hole_re.search(recovered_proof_term[search_start_idx:])
            if search:
                hole_idx_lst.append(search.start())

                prefix = proof_term_before[:search.start()]
                suffix = proof_term_before[search.end():]

                # print(find_parens(proof_term_after))
                # hole_term = proof_term_after[search.start():find_parens(proof_term_after)[search.start()]]
                # recovered_proof_term = re.sub(hole_re, hole_term, recovered_proof_term, count=1)
                
                # 去掉所有？Goal的idx，之后倒着match
                any_hole_re = re.compile(r'\?Goal(\d+)')
                
                after_temp = any_hole_re.sub('?Goal_', proof_term_after)
                # hold_end = len(after_temp) - after_temp[::-1].find(any_hole_re.sub('?Goal_', suffix)[::-1])  - 1
                # print('suffix', suffix)
                print('suffix', any_hole_re.sub('?Goal_', suffix))
                hold_end = list(find_all(after_temp, any_hole_re.sub('?Goal_', suffix)))[-1]

                print('hole_start', search.start())
                print('hold_end', hold_end)
                hole_term = proof_term_after[search.start():hold_end]

                # note that while goal holes positions don't change, numbering may change
                # find_suffix = list(find_all(proof_term_after, suffix))
                hole_lst.append(hole_term)

                
            else:
                break
        
        # SECOND STEP: match diff to holes
        # marked_idx = -1
        # for hole_idx in hole_idx_lst:
        #     matching = False
        #     hole = ''
        #     for j, each in enumerate(result[hole_idx:]):
        #         if matching == False:
        #             if each[0] == '+' and marked_idx < hole_idx + j:
        #                 hole += each[2:]
        #                 marked_idx = hole_idx + j
        #                 matching = True
        #             else:
        #                 continue
        #         else:
        #             if each[0] == '+':
        #                 hole += each[2:]
        #                 marked_idx = hole_idx + j
        #             else:
        #                 hole_lst.append(hole)
        #                 break
        

        
        # pprint(result)
        print(hole_lst)

        # for each in result:
        #     if each[0] == '+':
        #         hole += each[2:]
        #     else:
        #         continue

        # print(hole)

        recovered = proof_term_before
        for hole_term in hole_terms():
            if len(hole_lst) == 0:
                break
            recovered = recovered.replace(hole_term, hole_lst.pop(0))
        recovered = recovered.replace('?Goal_', '?Goal')
        proof_term_after = ' '.join(steps['proof_term_after'][0].replace('\n', ' ').split()) if len(steps['proof_term_after']) != 0 else ''

        any_hole_re = re.compile(r'\?Goal(\d*)')

        # recovered = any_hole_re.sub('?Goal', recovered)
        # proof_term_after = any_hole_re.sub('?Goal', proof_term_after)

        print(recovered)
        print('\n')
        print(proof_term_after)
        print('match??', recovered == proof_term_after)
        # assert recovered == proof_term_after
        # print(recovered_proof_term)

    break
