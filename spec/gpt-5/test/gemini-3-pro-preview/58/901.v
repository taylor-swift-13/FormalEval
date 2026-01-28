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
    [45.96597872747401; 53.3656861633342; -35.672903633043234] 
    [45.96597872747401; 53.3656861633342; -35.672903633043234] 
    [-35.672903633043234; 45.96597872747401; 53.3656861633342].
Proof.
  unfold common_spec.
  split.
  - repeat constructor.
    + simpl; intuition; lra.
    + simpl; intuition; lra.
    + simpl; intuition; lra.
  - split.
    + repeat constructor; simpl; try lra.
    + intros x.
      simpl.
      intuition; subst; try lra.
Qed.