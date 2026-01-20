Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  result = true <->
  exists (i j : nat),
    (i < length numbers)%nat /\
    (j < length numbers)%nat /\
    i <> j /\
    Rabs (nth i numbers 0 - nth j numbers 0) < threshold.

Example test_has_close_elements :
  has_close_elements_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold has_close_elements_spec.
  split.
  - intros _.
    exists 2%nat, 3%nat.
    simpl.
    repeat split.
    + lia.
    + lia.
    + lia.
    + unfold Rabs.
      destruct (Rcase_abs (3.9 - 4.0)).
      * lra.
      * lra.
  - intros _. reflexivity.
Qed.