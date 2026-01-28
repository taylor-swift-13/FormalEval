Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_long :
  problem_48_spec
    "aaWas it a car or a cat I saw?bWas it a car ostep on no petsr a ca t I saw?ca"
    false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hpal.
    exfalso.
    specialize (Hpal 1).
    assert (Hlt : (1 < String.length "aaWas it a car or a cat I saw?bWas it a car ostep on no petsr a ca t I saw?ca" / 2)%nat).
    { simpl. lia. }
    specialize (Hpal Hlt).
    simpl in Hpal.
    inversion Hpal.
Qed.