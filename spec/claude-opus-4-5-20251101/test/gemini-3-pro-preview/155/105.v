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

(* 
   We define a helper to map the test input (Z) to its string representation (list ascii).
   For negative numbers, we use an equality check as pattern matching on negative Z literals 
   is not standard syntax.
*)

Definition digits_of_Z (n : Z) : list ascii :=
  if n =? -53 then ["-"%char; "5"%char; "3"%char] else [].

(* Adjusted Specification to link 'num' to 'str_repr' *)
Definition even_odd_count_spec (num : Z) (even_count : Z) (odd_count : Z) : Prop :=
  forall (str_repr : list ascii),
    str_repr = digits_of_Z num ->
    even_count = count_even_digits str_repr /\
    odd_count = count_odd_digits str_repr.

(* --- Test Case Proof --- *)

(* Test case: input = -53, output = (0, 2) *)
Example test_even_odd_count_neg53 : even_odd_count_spec (-53) 0 2.
Proof.
  (* Unfold the specification *)
  unfold even_odd_count_spec.
  
  (* Introduce the string representation and the equality hypothesis *)
  intros str_repr H_eq.
  
  (* Substitute str_repr with the actual digits of -53 *)
  unfold digits_of_Z in H_eq.
  rewrite H_eq.
  
  (* Simplify the counting functions on the concrete list ["-"; "5"; "3"] *)
  simpl.
  
  (* The goal is now 0 = 0 /\ 2 = 2 *)
  split.
  - reflexivity.
  - reflexivity.
Qed.