Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert positive to binary string.
 * Uses structural recursion on positive numbers (binary representation).
 *)
Fixpoint pos_to_binary (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary p' ++ "0"
  | xI p' => pos_to_binary p' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion for Z.
 * Handles 0 explicitly and delegates positive numbers.
 *)
Definition Z_to_binary_string (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => pos_to_binary p
  | Zneg _ => "" (* Problem implies non-negative inputs *)
  end.

(* 
 * @brief Main implementation matching the specification.
 * Adds "db" prefix and suffix.
 *)
Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ Z_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

(* Test case verification *)
Example test_decimal_to_binary_large : problem_79_spec 1000000005 "db111011100110101100101000000101db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* 
     Use vm_compute for efficient computation with Z. 
     Standard simpl or compute would be too slow if using unary nat, 
     but with Z and vm_compute this is instantaneous.
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.