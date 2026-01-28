Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Open Scope string_scope.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_custom :
  problem_48_spec "Was it a car or a cat I saw?referranever oddWas it a car or a sacat I saw? venr" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros Hpal.
    exfalso.
    specialize (Hpal 0%nat).
    assert (Hlt: (0 < String.length "Was it a car or a cat I saw?referranever oddWas it a car or a sacat I saw? venr" / 2)%nat).
    { simpl. lia. }
    specialize (Hpal Hlt).
    simpl in Hpal.
    discriminate Hpal.
Qed.