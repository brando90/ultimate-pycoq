# Opam.py

Previous method of running a command was fragile to piping and chaining commands. This is a more robust method.

```python
command = "set -e; " + command

opam_command: str = f'opam exec --switch {switch} -- sh -c {shlex.quote(command)}'
```

There were several issues we needed to resolve:
 - just trying to run the command as `opam exec --switch {switch} -- make clean && make` would fail because the `&&` would be interpreted by the shell as to first run `opam exec --switch {switch} -- make clean` and then run `make` not in the opam environment. This is not what we want.
   - The solution is to wrap the command in a shell script and run that script with `opam exec --switch {switch} -- sh -c {shlex.quote(command)}`
   - We use `shlex.quote` from the standard library to escape the command robustly so that it is interpreted as a single argument to `sh -c`
 - We also need to make sure that the command fails if any of the commands in the chain fail. This is because we want to be able to catch the error and report it to the user. We don't want it hidden by the fact that the last command in the sequence succeeded.
   - However, we can't just check `stderr` for content since make will print warnings to `stderr` even if the command succeeds.
   - This is done by prepending `set -e;` to the command. This will cause the shell to exit if any of the commands in a chain or pipe fail.

# coqproject.py

This file is used to build a coq project and get the build order of the files and hold general information about a coq project.

The old method in u-pycoq was to use strace while building the project to get the file build order, the command line flags, and the environment variables from all the system calls made during the build process. However, this only works on Linux, requires building the entire project everytime (or storing a local file in the coq project).

From my testing though, it seems like we don't actually need any of the environment variables used during building:
 - OPAMSWITCH/OPAM_SWITCH_PREFIX/PWD (we set manually)
 - CAML_LD_LIBRARY_PATH/OCAML_TOPLEVEL_PATH (should only be important for internal opam stuff, should not affect us I think as long as we are constant with ocaml usage)
 - Other things like PATH would be system dependent anyway. We need to compile projects locally in the first place in order to include them in .v files and if paths/other things get changed, the stored environment would probably break more than not storing the environment


It turns out we can use the command `coqdep` to easily get the build order of the files in a coq project. This is much easier than trying to parse the `_CoqProject` file ourselves.

```bash
coqdep -f _CoqProject -sort -suffix .v
```
We can run this command using opam.py and then parse the output to get the build order.

The current method of getting build flags is to create a fresh copy of the coq makefile and then parse through the environment variables found in the generated .conf file.

We create a temporary file and generate the makefile using the command:
```bash
coq_makefile -f _CoqProject -o {temporary_file_name}
```
We can then parse the file `temporary_file_name.conf` to get the build flags. The important environment variables are COQMF_COQLIBS and COQMF_OTHERFLAGS which contain the -I/-R/-Q flags and every other coqc flag respectively.

An alternative approach would be to parse the _CoqProject file for the flags ourselves. This might be slightly faster (although this command runs in a fraction of a second already), but perhaps less robust to changes in coq version.

# Parse.py

This file parses coq files so we can iterate over each coq statement in a .v file.

### First Pass
The first pass was somewhat messy without any nice class interface. It only reads from the file one line at a time. The one big potential benefit of this is that it has a much lower memory footprint compared to reading in the entire file at once. However, it is a bit harder to read than the new approaches.

### Second Pass
I wanted to make a class interface because I think for something like this it is nicer to work with as a user. This pass also only read the file line by line, so it has a similar memory footprint to the first pass. However, it is much slower (~2.5x) than the first pass. I ran some basic profiling, and it seems like it is spending a lot of time in the `re` module. I think this is because it is compiling the regexes every time it is called. I think this is the main reason for the slowdown. I think this could be fixed by compiling the regexes once and then passing them to the class. However, I think the first pass is still better because it is faster and has a lower memory footprint despite being less unintuitive to use.

### Third pass
This pass reads the entire file into memory at once. This obviously has a much worse memory footprint. However the upside is that we can compute all the regex matches in one go which seems to be faster. Additionally, it seems like in total, reading in the entire file at once is faster than reading it is chunks. It is about 15% faster than the first pass. I think this is the best approach because it is fast and easy to use despite the higher memory footprint. We are working with text files so the memory footprint should not be too bad anyway.

# coqinterface.py

TODO: write this file
This file will let us interact with coq by sending coq statements and receiving responses. We should also be able to query goals and proofs (what else?)

One thing that would be nice is to be able to use different kernels that implement .add, .exec, etc. methods so we can try out different backends easily. This might not be so feasible though, as making the kernels each compatible with the same structure for use in the interface might be difficult. It would probably just be easier to write a separate interface for each kernel, especially for the difference between using coqidetop with xml and serapi with s-expressions (serapi and e-pycoq might be able to use the same interface). This requires experimentation.


# LSP vs SERAPI

## LSP pros
 - Document model is very easy to use down the line/very general
   - Only have to manage a single string of text and lsp manages parsing and recompiling
 - Probably more efficient than serapi
 - Barrier to entry for new project members is much lower

## LSP cons
 - Time/effort required to implement backend might be much more than serapi
 - Very little documentation (might be coming in near future)
 - Not fully functional yet (might be good enough for our purposes though)

## SERAPI pros
 - Already implemented
 - More documentation
 - Much easier to implement backend

## SERAPI cons
 - Deprecated in favor of LSP
 - Much less powerful then LSP
 - Requires more working knowledge of api internals to use
   - More work for new project members to get up to speed
 - Might be less efficient than LSP

# Current Evaluation Model
```
{scraper, eval} <-> [Pycoq]_py.api <-> [Kernal]_py.api
<-> [Specific Backend]_py.api <-> (Backend)_original_backend.api e.g. serapi, lsp
<-> (Coq, perhaps we don't care parenthesis) 

```

Training Data
 - (entire, partial) Proof Terms (execute coq stmts e.g. tactics)
 - coq files
 - proof state, tactic, partial proof
 - local lemmas
tasks: https://arxiv.org/abs/2102.06203 co-training 

Tasks ({scraper, eval} <-> [Pycoq]_py.api)
 - predict entire proof term from target theorem <x=tt,y=ept>
 - predict hole remaining proof term  (e.g. hole)/tactics/tactic/proof length from target theorem, proof state (local context, some global context) e.g <x=(tt, ps, gc), y=(ppt, tactic script, tactic, proof length ast, len proof # tactics)>

tt=target theorem
ept = entire proof term
ps = proof state
gc = global context
ppt = partial proof term

Evaluate (on HELM using string metrics, provers [e.g. Zero zero proof gen, Parsel])
 - avg/exact string accuracy, perplexity/loss
 - Proving accuracy using a prover