Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpal :
  problem_48_spec "Was it a car or a cat I saw?refer" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. discriminate H.
  - intros Hpal.
    exfalso.
    assert (Hlt: (0 < (String.length "Was it a car or a cat I saw?refer") / 2)%nat).
    { simpl; lia. }
    specialize (Hpal 0 Hlt).
    simpl in Hpal.
    congruence.
Qed.