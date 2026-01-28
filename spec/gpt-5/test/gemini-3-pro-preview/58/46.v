Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition common_spec (l1 l2 out : list R) : Prop :=
  NoDup out
  /\ Sorted Rle out
  /\ forall x : R, In x out <-> (In x l1 /\ In x l2).

Example test_common_spec : 
  common_spec 
    [72.37521383648374; 75.77463522981091; -68.50801238200772; -16.457158264907306; -14.710649879972792; -50.826346308865425; 94.08151854781187; 62.25940015569594; -16.457158264907306] 
    [72.37521383648374; 75.77463522981091; -68.50801238200772; -16.457158264907306; -14.710649879972792; -50.826346308865425; 94.08151854781187; 62.25940015569594; -16.457158264907306] 
    [-68.50801238200772; -50.826346308865425; -16.457158264907306; -14.710649879972792; 62.25940015569594; 72.37521383648374; 75.77463522981091; 94.08151854781187].
Proof.
  unfold common_spec.
  split.
  - (* Prove NoDup out *)
    repeat constructor; simpl; intuition; try lra.
  - split.
    + (* Prove Sorted Rle out *)
      repeat constructor; simpl; try lra.
    + (* Prove the equivalence of inclusion *)
      intros x.
      simpl.
      intuition; subst; try lra.
Qed.