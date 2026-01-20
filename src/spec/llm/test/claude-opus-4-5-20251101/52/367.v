Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (5.5 :: 7.9 :: nil) (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    assert (In 5.5 (5.5 :: 7.9 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 5.5 Hin).
    lra.
Qed.