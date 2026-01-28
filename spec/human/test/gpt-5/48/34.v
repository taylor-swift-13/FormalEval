Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Lia.
Open Scope string_scope.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_case :
  problem_48_spec "aaWas it a car or a cat I rbWas it a car ostep on no petsr a cafrefer t I saw?ca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros Hfalse i Hi.
    exfalso.
    discriminate Hfalse.
  - intros Hpal.
    specialize (Hpal 1%nat).
    assert (Hlt : (1 < String.length "aaWas it a car or a cat I rbWas it a car ostep on no petsr a cafrefer t I saw?ca" / 2)%nat).
    { simpl. lia. }
    specialize (Hpal Hlt).
    simpl in Hpal.
    exfalso.
    congruence.
Qed.