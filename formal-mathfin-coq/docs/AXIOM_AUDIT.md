# Axiom audit

The first slice was compiled and checked with Rocq 9.1.1.

`Print Assumptions` on the three audited theorems reports:

- `ClassicalDedekindReals.sig_forall_dec`;
- `FunctionalExtensionality.functional_extensionality_dep`.

These assumptions come from Rocq's standard classical real-number
implementation and the tactics/theorems used with it; they are not
project-local axioms.

The transitive `rocq check -o MathFin.AxiomAudit` module context additionally
contains:

- `ClassicalDedekindReals.sig_not_dec`;
- `Classical_Prop.classic`.

The kernel checker reports:

- no `type-in-type` dependencies;
- no unsafe fixpoints or cofixpoints;
- no assumed positivity for inductive definitions;
- rewrite rules disabled.

This differs from the Lean upstream's standard axiom set and is therefore
recorded explicitly. A later move to a constructive real-number library would
change the statements' computational behavior and must be evaluated as a
deliberate dependency migration.
