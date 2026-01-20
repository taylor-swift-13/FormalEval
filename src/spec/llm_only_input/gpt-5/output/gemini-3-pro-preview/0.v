Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  result = true <->
  exists (i j : nat),
    (i < length numbers)%nat /\
    (j < length numbers)%nat /\
    i <> j /\
    Rabs (nth i numbers 0 - nth j numbers 0) < threshold.

Example has_close_elements_spec_test :
  has_close_elements_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 0.3%R true.
Proof.
  unfold has_close_elements_spec.
  split.
  - intros _.
    exists 2%nat, 3%nat.
    repeat split.
    + simpl; lia.
    + simpl; lia.
    + lia.
    + simpl.
      assert (Hdiff: 3.9%R - 4.0%R = -0.1%R) by lra.
      rewrite Hdiff.
      rewrite Rabs_Ropp.
      rewrite Rabs_pos_eq; [lra | lra].
  - intros _. reflexivity.
Qed.