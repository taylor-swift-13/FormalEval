Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_frefer :
  problem_48_spec "frefer"%string false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros HP. exfalso.
    assert (Hlt : (0 < String.length "frefer"%string / 2)%nat) by (simpl; lia).
    specialize (HP 0 Hlt).
    simpl in HP.
    injection HP as Hch.
    discriminate Hch.
Qed.