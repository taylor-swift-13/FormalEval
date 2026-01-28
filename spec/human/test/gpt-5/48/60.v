Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpal :
  problem_48_spec "reWas it a car or a catw Ir saw?fer" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hpal.
    exfalso.
    specialize (Hpal 2%nat).
    assert (Hlt: (2 < String.length "reWas it a car or a catw Ir saw?fer" / 2)%nat) by (simpl; lia).
    specialize (Hpal Hlt).
    simpl in Hpal.
    discriminate Hpal.
Qed.