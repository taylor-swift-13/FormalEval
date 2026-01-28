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

Example test_problem_48 : problem_48_spec "never odd or  even" false.
Proof.
  unfold problem_48_spec.
  simpl.
  split.
  - (* -> direction: Assume false=true (contradiction) *)
    intros H.
    inversion H.
  - (* <- direction: Assume the quantifier, prove false=true (contradiction) *)
    intros H.
    (* We find a counter-example at index 4 ('r' vs ' ') *)
    specialize (H 4).
    simpl in H.
    (* Prove the condition 4 < 9 *)
    assert (H_cond : (4 < 9)%nat).
    { repeat constructor. }
    apply H in H_cond.
    (* H_cond implies "r" = " ", which is false *)
    discriminate H_cond.
Qed.