"""
Defines the proof script class. Allows for the management and editing of proof scripts.
"""


class Statement:
    def __init__(self, statement: str, range: tuple, proof_status: str, partial_proof_term: str, goals: list):
        self.statement = statement
        self.range = range
        self.proof_status = proof_status
        self.partial_proof_term = partial_proof_term
        self.goals = goals


class ProofScript:
    def __init__(self, path: str, lsp_client):
        self.path = path
        if path == '':
            self.document = ''
        else:
            self.document = open(path, 'r').read()

        self.version = 1

        self.lsp_client = lsp_client
        self.statements: list[Statement] = []

    def update_document(self):
        """
        Notifies the LSP client of a document change. Updates the proof script's statements where needed.
        :return: None
        """
        self.version += 1
        self.lsp_client.notify('textDocument/didChange', {
            'textDocument': {
                'uri': self.path,
                'version': self.version
            },
        })

    def update_statements(self):
        """
        Updates the proof script's statements.
        :return: None
        """
        self.statements = []
        for statement in self.lsp_client.get_statements():
            self.statements.append(Statement(statement['statement'], statement['range'], statement['proof_status'], statement['partial_proof_term'], statement['goals']))


def example_proof_script():
    lsp_client = None  # todo
    proof_script = ProofScript('', lsp_client)
    # Edit the proof script
    proof_script.document += "reflexivity.\nQed."
    proof_script.update_document()

    for statement in proof_script.statements:
        # where in proof_script.script is the statement located
        statement_range = statement.range

        # Retrieve proof status
        proof_status = statement.proof_status

        # Handle proof-related metadata
        partial_proof_term = statement.partial_proof_term
        goals = statement.goals


if __name__ == '__main__':
    example_proof_script()