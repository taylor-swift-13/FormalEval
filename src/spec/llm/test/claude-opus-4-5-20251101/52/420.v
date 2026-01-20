Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (0 :: 62 :: -64 :: 0 :: 98 :: 0 :: -51 :: 58 :: 55 :: 10 :: nil) 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    assert (H1 : In 62 (0 :: 62 :: -64 :: 0 :: 98 :: 0 :: -51 :: 58 :: 55 :: 10 :: nil)).
    { simpl. right. left. reflexivity. }
    specialize (H 62 H1).
    lia.
Qed.