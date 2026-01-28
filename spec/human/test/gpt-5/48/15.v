Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_was_it_a_car_or_a_cat_i_saw :
  problem_48_spec "Was it a car or a cat I saw?" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. inversion H.
  - intros H.
    assert (0 < String.length "Was it a car or a cat I saw?" / 2)%nat.
    { simpl. lia. }
    specialize (H 0%nat H0).
    simpl in H.
    discriminate H.
Qed.