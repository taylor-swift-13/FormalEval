Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_non_pal :
  problem_48_spec "Was it a car orWas it a car or a cat I saw?r a sacat I saw?" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros HP.
    exfalso.
    assert (Hlt : (0 < String.length "Was it a car orWas it a car or a cat I saw?r a sacat I saw?" / 2)%nat).
    { simpl. lia. }
    specialize (HP 0 Hlt).
    simpl in HP.
    discriminate HP.
Qed.