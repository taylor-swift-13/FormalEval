Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_long :
  problem_48_spec "Was it a car or I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?refer" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    assert (Hi0 : (0 < String.length "Was it a car or I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?refer" / 2)%nat).
    { simpl. lia. }
    specialize (H 0 Hi0).
    simpl in H.
    discriminate H.
Qed.