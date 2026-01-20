Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_is_palindrome_empty :
  Spec EmptyString true.
Proof.
  unfold Spec.
  split.
  - intro H.
    intros i H_bound.
    simpl in H_bound.
    lia.
  - intro H.
    reflexivity.
Qed.