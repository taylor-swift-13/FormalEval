Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Arith.

Import ListNotations.
Open Scope Z_scope.

(* --- Provided Definitions --- *)

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

(* --- Helper Functions for Test Case --- *)
(* To prove the test case relating a Z number to counts of digits, 
   we need a way to convert Z to a list of ascii characters. *)

Fixpoint nat_to_list_ascii_aux (n : nat) (fuel : nat) : list ascii :=
  match fuel with
  | 0%nat => []
  | S f =>
    if Nat.ltb n 10 then [ascii_of_nat (48 + n)]
    else (nat_to_list_ascii_aux (n / 10)%nat f) ++ [ascii_of_nat (48 + (n mod 10)%nat)]
  end.

Definition Z_to_list_ascii (z : Z) : list ascii :=
  match z with
  | Z0 => ["0"%char]
  | Zpos p => nat_to_list_ascii_aux (Pos.to_nat p) (Pos.to_nat p)
  | Zneg p => "-"%char :: nat_to_list_ascii_aux (Pos.to_nat p) (Pos.to_nat p)
  end.

(* --- Specification --- *)
(* The specification links the input number to the expected counts 
   by converting the number to its string representation. *)

Definition even_odd_count_spec (num : Z) (even_count : Z) (odd_count : Z) : Prop :=
  let str_repr := Z_to_list_ascii num in
  even_count = count_even_digits str_repr /\
  odd_count = count_odd_digits str_repr.

(* --- Test Case Proof --- *)
(* Input: 7, Output: (0, 1) *)

Example test_even_odd_count_7 : even_odd_count_spec 7 0 1.
Proof.
  (* Unfold the specification to see the definitions *)
  unfold even_odd_count_spec.
  
  (* Unfold the conversion logic *)
  unfold Z_to_list_ascii.
  
  (* Simplify the computation. 
     7 is converted to "7", which is an odd digit. *)
  simpl.
  
  (* Verify both parts of the conjunction:
     0 = 0 (even count) and 1 = 1 (odd count) *)
  split; reflexivity.
Qed.