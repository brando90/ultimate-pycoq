import torch

import pytp.coq

"""
Thoughts (06/28/23) for an interactive enviornment between a LLM agent and Coq

The proving agent:
    We should have a standard framework for the interacting LLM agents, need instruction templates, mapping between LLM outputs and actual proof lines to be sent to coq:
    two kinds of generative LLM: 1) sentence completion. 2) Chat. Their outputs need different parsing rules

The gym should provide:
1) basic interaction loop between the agent and coq
2) evaluation of agent's performance given some metrices
3) optional layer of parsing and translation between coq input and output and LLM-friendly prompts
4) optional exception handleing to make training and testing less prone to give-ups

gym loop:
    gym-master -> proving agent [coq output handler -> main LLM -> LLM output handler] -> gym-master

expected model ouputs, and mode of interaction:
    1) the model works on a proof file as if a person would write it. the model "COMPLETES" the proof started by some given theorem to be proven. The model receives feedback from coq with each additional line it completes.
    2) the model 'CHAT' about a proof task. The model receives the proof script (current progress of the proof) as part of an instruction prompt. The model respond to the intruction, and some algorithm handles the communication with coq. With each edit to the proof script, the model receives new instruction as generated according to coq reponses.
"""
