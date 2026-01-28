Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_aabc :
  problem_48_spec "aabc" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros H.
    assert (String.get 0 "aabc" <> String.get (String.length "aabc" - 1 - 0) "aabc") as Hneq.
    { intros EQ. simpl in EQ. discriminate EQ. }
    assert (0 < String.length "aabc" / 2)%nat as Hlt by (simpl; lia).
    specialize (H 0%nat Hlt).
    apply Hneq in H.
    exfalso.
    exact H.
Qed.