Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_aabca :
  problem_48_spec "aabca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    assert (String.get 1%nat "aabca" <> String.get (String.length "aabca" - 1 - 1)%nat "aabca") as Hneq.
    { simpl. discriminate. }
    specialize (H 1%nat).
    assert (1 < String.length "aabca" / 2)%nat by (simpl; lia).
    specialize (H H0).
    apply Hneq in H.
    exact H.
Qed.