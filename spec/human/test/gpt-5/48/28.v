Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Local Open Scope string_scope.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpal :
  problem_48_spec "reWas it a car or a cat I saw?fer" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros Hfalse i Hi. discriminate Hfalse.
  - intros H.
    exfalso.
    simpl in H.
    specialize (H 2%nat).
    assert (2 < 16)%nat by lia.
    specialize (H H0).
    simpl in H.
    injection H as Heq.
    inversion Heq.
Qed.