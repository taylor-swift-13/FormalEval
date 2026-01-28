Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_case :
  problem_48_spec "aaWas it a car or a cat I rbWas it a car ostep on no petsr a ca t I saw?ca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. discriminate H.
  - intros Hprop.
    assert (Hlt : (1 < String.length "aaWas it a car or a cat I rbWas it a car ostep on no petsr a ca t I saw?ca" / 2)%nat).
    { simpl. lia. }
    specialize (Hprop 1 Hlt).
    simpl in Hprop.
    injection Hprop as Hac.
    congruence.
Qed.