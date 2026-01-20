Require Import List Arith.
Import ListNotations.

Definition Pre := True.

Definition Spec (input output : list nat) :=
  length output = length input /\
  forall i,
    i < length output ->
    (forall j, j <= i -> nth j input 0 <= nth i output 0) /\
    (exists j, j <= i /\ nth j input 0 = nth i output 0).

Example test_case : Spec [] [].
Proof.
  unfold Spec.
  split.
  - reflexivity.
  - intros i Hi.
    split.
    + intros j Hj.
      inversion Hi.
    + inversion Hi.
Qed.