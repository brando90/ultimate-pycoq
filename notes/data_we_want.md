# Data we want to extract from Coq

Definitions:
`ps := proof_state := <local_context, goals>`
`ept := entire_proof_term`
`ppt := partial_proof_term`
`hts := hole_terms`
`NL := Natural Language`
`FL := Formal Language`

1. `<prev_tac, proof_state, next_tac>` (if possible `global_context` too)
2. `<prev_tactic_script, proof_state, remainign_tacic_script>` (if possible `global_context` too). (meant to help user with suggestion about the remaining tactic script)
3. `<proof_state, entire_proof_term>` (this includes when proof state is just the top level `theorem` or `lemma` etc. so entire_proof)
4. `<proof_state, partial_proof_term, hole_terms>` this means the parital proof term for the current goal (e.g., top level theorem too) and the holes to complete the proof. Ideally not only the tactic (or hammer), the actual proof term.


Don't forget:
1. `lemma`s, `examples`, functions (since proofs are program and the types are theorems), NL comments, anything that can help 1. prove more 2. autoformalize
2. wherever possible getting gloabl context is nice (Coq has a ML tool to do this, some tactic).
3. Ideally all the data we can get as this paper did or more: https://arxiv.org/abs/2102.06203
4. getting the data shown in important built ins e.g., the type and program of the induction tactic.
5. Generizing the inductive hypothesis

Bellow is the data we want, ref: https://arxiv.org/abs/2102.06203 feel free to suggest anything if you think I missed something.

## 3.2. PROOF ARTIFACT CO-TRAINING

In this section, we describe the PACT task suite and how data for these tasks are extracted.

For every proof term $\tau$, we record the type $\Gamma$ of $\tau$, its name nm, and a list ps of all premises (i.e. named references to other lemmas in the library) which are used in $\tau$. We then recurse through $\tau$, tracking a list bs of bound variables which we update whenever navigating into the body of a $\lambda$-expression. At every sub-term $\tau^{\prime} \subseteq \tau$ we record $\tau^{\prime}$, its type $\Gamma^{\prime}$, the current state of bs, and the following data:

1. A tactic state, where the goal is set to be $\Gamma^{\prime}$ and the list of hypotheses in the local context is set to be the list bs, i.e. those bound variables in scope at $\tau^{\prime}$.
2. A partial proof term, i.e. $\tau$ with $\tau^{\prime}$ masked out.
3. A premise selection bitmask, i.e. Boolean labels for every $\mathrm{p}$ in $\mathrm{ps}$ indicating whether $\mathrm{p}$ is used in $\tau^{\prime}$.
4. A local context bitmask, i.e. similar Boolean labels for every $\mathrm{b}$ in bs indicating whether $\mathrm{b}$ is used in $\tau^{\prime}$.
5. An optional next lemma: if the first step of $\tau^{\prime}$ is to apply a premise $\mathrm{p}$ in $\mathrm{ps}$, we record $\mathrm{p}$.

Whenever we record a term, we record both pretty-printed and far more explicit fully elaborated versions of it. The fully elaborated terms explicitly display enormous amounts of type information which are usually silently inferred by Lean. From these data, we assemble the following language modeling tasks:

1. Next lemma prediction. Given the tactic state, predict the next lemma to be applied.
2. Proof term prediction. Given the tactic state, predict the entire proof term $\tau^{\prime}$.
3. Skip-proof. Given the partial proof term, predict the masked subterm $\tau^{\prime}$.
4. Type prediction. Given the partial proof term, predict the type $\Gamma^{\prime}$ of the masked subterm $\tau^{\prime}$.
5. Tactic state elaboration. Given the tactic state, predict the fully elaborated tactic state.
6. Proof term elaboration. Given $\tau$, predict the fully elaborated version of $\tau$.
7. Premise classification. Given the tactic state and a premise $p \in p s$, predict either $\langle$ TRUE $>$ or $\angle F A L S E>$ according to the premise selection bitmask.
8. Local context classification. Given the tactic state (which consists of a list of local assumptions bs and the goal $\Gamma^{\prime}$ ), predict the sublist of bs which is true on the local context bitmask.
9. Theorem naming. Given the type $\Gamma$ of the top-level proof term $\tau$, predict the name nm.

We remark that our next lemma prediction task is precisely the low-level PROOFSTEP objective studied in (Polu \& Sutskever, 2020), and our skip-proof task superficially resembles, but is much more difficult than the skip-tree task studied in (Rabe et al. 2021), as proof terms tend to be far more complex than the syntax trees of theorem statements.

