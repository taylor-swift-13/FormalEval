Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < IZR t).

Example test_below_threshold: below_threshold_spec [5.871122108907659%R; 6.2%R; 7.9%R] 301%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    destruct H as [H | [H | [H | []]]]; subst; lra.
  - intros _.
    reflexivity.
Qed.