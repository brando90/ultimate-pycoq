# Why serapi to build PyCoq

To be honest I'm not sure we need serapi. 
Initially I used it because I thought it was the right way to talk to coq through python.
I learned that serapi is complicated and outputs unepxected things, that breaks my serapi-pycoq interface.
I thought Vasily's PyCoq would work, but it doesn't.
Is it worth sticking with serapi based PyCoq?
It's hard to know.
At least we have code that seems to be close to working but has some issues:
- (originally) it had a deadlock with constructive geometry with complicated tactics
- (origianlly) it also didn't work the weird hacking solution to extract partial proof terms (I strongly suggest we move to unfication based one for this)
- now the induction import/require isn't working
- nor is the proof term extraction at the end of a proof. Perhaps I'm just calling a proof extraction term too son, while I should only do it at the end of the proof.
it will be nice to figure out which issues are due to serapi and which are due to bad processing of files.
Also, Vasily's way to extract statements from coq seemed useful, so not building a parser for that ourselves seems useful.
As any research project it's hard to know how to proceed but given that serapi is deprecated perhaps its good to abandon it.
Maybe for the short term it's fine but moving to lsp-pycoq is likely the best way forward.

ref:
    - https://github.com/ejgallego/coq-serapi/issues/332