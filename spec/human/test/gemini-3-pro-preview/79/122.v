Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert positive to binary string representation.
 * Recursively constructs the binary string.
 *)
Fixpoint pos_to_binary_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary_string p' ++ "0"
  | xI p' => pos_to_binary_string p' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion for Z.
 * Handles 0 explicitly.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary_string p
  | Zneg _ => "" 
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
Example test_decimal_to_binary_large : problem_79_spec 274877906939 "db11111111111111111111111111111111111011db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* 
     Use vm_compute for efficient evaluation of large numbers.
     Standard simpl or compute would be too slow for this input size if using nat,
     but with Z and vm_compute it is instantaneous.
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.