Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  (*
    output is true if and only if:
    for all natural numbers i, if i is less than half the string length,
    then the character at position i must equal the character at position (length - 1 - i).
  *)
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_problem_48 : problem_48_spec "aabca" false.
Proof.
  unfold problem_48_spec.
  split.
  - (* -> direction: Assume false=true, prove the quantifier *)
    intros H.
    inversion H.
  - (* <- direction: Assume the quantifier, prove false=true *)
    intros H.
    (* We need to show that the assumption leads to a contradiction.
       The string is "aabca", length 5. length/2 = 2.
       We check index i = 1.
       get 1 is 'a', get (5-1-1)=3 is 'c'.
       'a' != 'c', so the quantifier must be false. *)
    assert (H_cond : (1 < String.length "aabca" / 2)%nat).
    { simpl. auto. }
    specialize (H 1 H_cond).
    simpl in H.
    inversion H.
Qed.