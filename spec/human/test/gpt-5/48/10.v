Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_abc :
  problem_48_spec "abc" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi. exfalso. discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (Hi : (0 < (String.length "abc") / 2)%nat).
    { simpl. lia. }
    specialize (H Hi).
    simpl in H.
    congruence.
Qed.