Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpal :
  problem_48_spec "Was it a car ostep on no petsr a ca t I saw?"%string false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hpal.
    exfalso.
    specialize (Hpal 0%nat).
    assert (Hlt : (0 < (String.length "Was it a car ostep on no petsr a ca t I saw?"%string) / 2)%nat) by (simpl; lia).
    specialize (Hpal Hlt).
    simpl in Hpal.
    congruence.
Qed.