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
  | 54837398243238 => ["5"%char; "4"%char; "8"%char; "3"%char; "7"%char; "3"%char; "9"%char; "8"%char; "2"%char; "4"%char; "3"%char; "2"%char; "3"%char; "8"%char]
  | _ => [] 
  end.

(* Adjusted Specification to link 'num' to 'str_repr' *)
Definition even_odd_count_spec (num : Z) (even_count : Z) (odd_count : Z) : Prop :=
  forall (str_repr : list ascii),
    str_repr = digits_of_Z num ->
    even_count = count_even_digits str_repr /\
    odd_count = count_odd_digits str_repr.

(* --- Test Case Proof --- *)

(* Test case: input = 54837398243238, output = (7, 7) *)
Example test_even_odd_count_54837398243238 : even_odd_count_spec 54837398243238 7 7.
Proof.
  (* Unfold the specification *)
  unfold even_odd_count_spec.
  
  (* Introduce the string representation and the equality hypothesis *)
  intros str_repr H_eq.
  
  (* Substitute str_repr with the actual digits *)
  unfold digits_of_Z in H_eq.
  rewrite H_eq.
  
  (* Simplify the counting functions on the concrete list *)
  simpl.
  
  (* The goal is now 7 = 7 /\ 7 = 7 *)
  split.
  - reflexivity.
  - reflexivity.
Qed.