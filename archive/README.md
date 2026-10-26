# Archive

These files are earlier stages of the formalization. The current theory is `../UPBJurisdiction.lean`, and its premises, conclusions and limitations are described in `../Premises.md`, `../Conclusions.md` and `../Limitations.md`. Nothing in the current theory depends on these files. They still compile as part of `lake build`.

- **`UPBProof.lean`** is the original formalization that the review began with. It relies on an agent-symmetry premise (P2) and a "mutual coercion" conflict, both of which the current theory drops. Its theorems are valid given its premises, but those premises are not the current ones.
- **`UPBSymmetry.lean`** shows why P2 was dropped. Its main result is `neutrality_does_not_imply_P2`: there is an agent-neutral rule ("the stronger may take from the weaker") that satisfies the other premises but violates P2. So P2 is strictly stronger than the principle that no one is privileged by name. Its last two theorems, bodily and property non-aggression without P2, are early versions of results the current theory proves in a richer model.
