Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_xywyz :
  problem_48_spec "xywyz" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hall.
    specialize (Hall 0%nat).
    assert (Hlt: (0 < String.length "xywyz" / 2)%nat) by (simpl; lia).
    specialize (Hall Hlt).
    simpl in Hall.
    exfalso.
    congruence.
Qed.