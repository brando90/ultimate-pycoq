# Opam.py

Previous method of running a command was fragile to piping and chaining commands. This is a more robust method.

```python
command = "set -e; " + command

opam_command: str = f'opam exec --switch {switch} -- sh -c {shlex.quote(command)}'
```

There were several issues we needed to resolve:
 - just trying to run the command as `opam exec --switch {switch} -- make clean && make` would fail because the `&&` would be interpreted by the shell as to first run `opam exec --switch {switch} -- make clean` and then run `make` not in the opam environment. This is not what we want.
   - The solution is to wrap the command in a shell script and run that script with `opam exec --switch {switch} -- sh -c {shlex.quote(command)}`
   - We use `shlex.quote` to escape the command robustly so that it is interpreted as a single argument to `sh -c`
 - We also need to make sure that the command fails if any of the commands in the chain fail. This is because we want to be able to catch the error and report it to the user. We don't want it hidden by the fact that the last command in the sequence succeeded.
   - However, we can't just check `stderr` for content since make will print warnings to `stderr` even if the command succeeds.
   - This is done by prepending `set -e;` to the command. This will cause the shell to exit if any of the commands in a chain or pipe fail.