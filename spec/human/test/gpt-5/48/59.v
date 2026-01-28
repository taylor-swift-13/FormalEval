Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpal :
  problem_48_spec "bWas it a car ostep on no petsr a ca t I saw?abbabcca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi. exfalso. discriminate H.
  - intros H.
    exfalso.
    assert (H0 : (0 < String.length "bWas it a car ostep on no petsr a ca t I saw?abbabcca" / 2)%nat).
    { simpl. lia. }
    specialize (H 0%nat H0).
    simpl in H.
    congruence.
Qed.