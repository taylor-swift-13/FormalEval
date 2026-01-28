Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_ab :
  problem_48_spec "ab" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros Hprop.
    exfalso.
    assert (Hneq : String.get 0 "ab" <> String.get 1 "ab").
    { simpl. discriminate. }
    specialize (Hprop 0).
    simpl in Hprop.
    assert (Hlt : (0 < String.length "ab" / 2)%nat) by (simpl; lia).
    specialize (Hprop Hlt).
    simpl in Hprop.
    apply Hneq in Hprop.
    exact Hprop.
Qed.