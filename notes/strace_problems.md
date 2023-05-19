# Strace problems in serapi-coq

Straces gives issues because:
- it doesn't work in mac (m1 or intel), only linux
I think it was needed because it gave us the topological sort of the coq .v files, so we could actually extract data from them in python.
However, this info can be obtained differently. 
Kai is going to test it using `coqdep`.

ref:
- https://stackoverflow.com/questions/73724074/how-to-call-an-equivalent-command-to-strace-on-mac-ideally-from-python