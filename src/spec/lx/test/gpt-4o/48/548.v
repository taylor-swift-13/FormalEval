Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_single_char :
  Spec "r" true.
Proof.
  unfold Spec.
  split.
  - intros _.
    intros i Hi.
    simpl in Hi.
    inversion Hi.
  - intros _.
    reflexivity.
Qed.