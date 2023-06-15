"""
# Initialize the LSP client
with ProofScript("path/to/proof.script") as proof_script:

    # Edit the proof script
    proof_script.script += "reflexivity.\nQed."

    for statement in proof_script.statements:
        # where in proof_script.script is the statement located
        statement_range = statement.range

        # Retrieve proof status
        proof_status = statement.proof_status

        # Handle proof-related metadata
        partial_proof_term = statement.partial_proof_term
        goals = statement.goals
"""
# Class representation for a interactive proof script (e.g. coq)
class ProofScript:

    def __init__(self, path: str = ''):
        # path: Path = Path(path).expanduser()
        self.path: str = path
        self.document: str = ''


def proof_script_example():
    example_proof_script: str = """
Theorem add_easy_induct_1:
forall n:nat,
  n + 0 = n.
Proof.
Show Proof. 
  intros.
Show Proof.
  induction n as [| n' IH].
Show Proof.
  - simpl.
Show Proof.
    reflexivity.
Show Proof.
  - simpl.
Show Proof.
    rewrite -> IH.
Show Proof.
    reflexivity.
Show Proof.
Qed.
"""
    coq_lsp: LSPClient = CoqLSPClient()
    proof_script: ProofScript = ProofScript(coq_lsp)
    # Edit the proof script, note: this client is editing this proof_script object
    proof_script.document = example_proof_script
    response = await proof_script.check_document()
    # todo if response error raise or do it inside check_document

    for statement in proof_script.statements:
        # where in proof_script.script is the statement located
        statement_range = statement.range

        # Retrieve proof status
        proof_status = statement.proof_status

        # Handle proof-related metadata
        partial_proof_term = statement.partial_proof_term
        goals = statement.goals


if __name__ == '__main__':
    proof_script_example()