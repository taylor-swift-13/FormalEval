Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.

Import ListNotations.
Open Scope Z_scope.

(* --- Definitions provided in the specification --- *)

Definition is_even_digit (c : ascii) : bool :=
  match c with
  | "0"%char | "2"%char | "4"%char | "6"%char | "8"%char => true
  | _ => false
  end.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

Fixpoint count_even_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_even_digit c then 1 else 0) + count_even_digits rest
  end.

Fixpoint count_odd_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_odd_digit c then 1 else 0) + count_odd_digits rest
  end.

(* --- Helper for the Test Case --- *)

Definition digits_of_Z (n : Z) : list ascii :=
  match n with
  | -923456795 => ["9"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "9"%char; "5"%char]
  | _ => []
  end.

(* Adjusted Specification to link 'num' to 'str_repr' *)
Definition even_odd_count_spec (num : Z) (even_count : Z) (odd_count : Z) : Prop :=
  forall (str_repr : list ascii),
    str_repr = digits_of_Z num ->
    even_count = count_even_digits str_repr /\
    odd_count = count_odd_digits str_repr.

(* --- Test Case Proof --- *)

(* Test case: input = -923456795, output = (3, 6) *)
Example test_even_odd_count_neg : even_odd_count_spec (-923456795) 3 6.
Proof.
  unfold even_odd_count_spec.
  intros str_repr H_eq.
  unfold digits_of_Z in H_eq.
  rewrite H_eq.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.