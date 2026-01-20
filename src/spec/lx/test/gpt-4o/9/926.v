Require Import List Arith.
Import ListNotations.

Definition Pre := True.

Definition Spec (input output : list nat) :=
  length output = length input /\
  forall i,
    i < length output ->
    (forall j, j <= i -> nth j input 0 <= nth i output 0) /\
    (exists j, j <= i /\ nth j input 0 = nth i output 0).

Example rolling_max_test_case :
  Spec [26; 0; 5; 12; 15; 5] [26; 26;26].
Proof.