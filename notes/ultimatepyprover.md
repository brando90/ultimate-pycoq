# UltimatePyProver API Design Document

_Name to be determined_

## Introduction:
The UltimatePyProver library is a Python package that provides an interface for interacting with theorem prover software through the Language Server Protocol (LSP). It allows users to edit proof scripts, automatically update metadata, retrieve proof status, and manage proof-related information.

## Architecture:
The library consists of two main components: the language server protocol client and the proof script interface. The LSP client handles the communication with the theorem prover subprocess via LSP, while the proof script interface provides an abstraction layer for editing and interacting with the proof script.

## LSP Client:
- `UltimatePyProver()` class is used to initialize the LSP client.
- The LSP client supports standard LSP features such as establishing connections, handling requests, notifications, and responses.
- Additional methods are provided to manage proof-related metadata and interact with the proof script interface as each theorem prover software may have different custom LSP methods.
- The LSP client establishes a subprocess connection to the theorem prover software, allowing bidirectional communication.

## Proof Script Interface:
- `ProofScript` class represents a proof script file.
- The proof script interface allows users to edit the proof script using the `script` property. `script` is a string that contains the contents of the proof script.
- Changes made to the proof script trigger automatic updates to the metadata through interactions with the LSP client (perhaps should require a manual call to trigger updates rather than automatic?).
- Users can iterate over the statements in the proof script using the `statements()` method.

# Proof Project Management:
 - The library provides methods to manage proof projects, such as creating, opening, and closing projects.
 - The `ProofProject` class represents a proof project.
 - It contains a list of proof scripts and provides methods to add, remove, and retrieve proof scripts.
 - This class is not required for the proof script interface to work, but it provides a convenient way to manage proof scripts when working with multiple files as it handles dependencies between files.

## Statement Metadata Management:
- The library maintains metadata about the proof, such as proof status, dependencies, and goals.
- The metadata is stored as properties of the `Statement` class.
- Proof-related metadata is automatically updated when changes are made to the proof script.
- Users can retrieve proof status using the `proof_status` property of a statement.
- The `goals` property returns the current goals for a statement.
- The `partial_proof_term` property returns the partial proof term for a statement.
- Other properties to be added as needed.

## Error Handling:
- Exceptions are raised to signal any errors encountered during communication, parsing, or validation.
  - When should they be ignorable?

## Usage Examples:
```python
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
```

## Dependencies:
- Specific versions and configurations of the theorem prover software may be required.

## Future Enhancements:
- Integration with other theorem prover software (not just coqlsp).

This is a draft version of the API design document. Feel free to refine and expand it further.