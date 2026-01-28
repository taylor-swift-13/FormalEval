Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Local Open Scope string_scope.
Local Open Scope N_scope.

(* 
 * @brief Helper function to convert positive to binary string representation.
 * Uses structural recursion on positive numbers (bits).
 *)
Fixpoint pos_to_binary (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary p' ++ "0"
  | xI p' => pos_to_binary p' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly.
 *)
Definition N_to_binary_string (n : N) : string :=
  match n with
  | N0 => "0"
  | Npos p => pos_to_binary p
  end.

(* 
 * @brief Main implementation matching the specification.
 * Adds "db" prefix and suffix.
 *)
Definition decimal_to_binary_impl (decimal : N) : string :=
  "db" ++ N_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : N) : Prop := True.

Definition problem_79_spec (decimal : N) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

(* Test case verification for large input *)
Example test_decimal_to_binary_large : problem_79_spec 999999996 "db111011100110101100100111111100db".
Proof.
  (* 
     Use vm_compute for efficient computation with large numbers (N).
     The standard simpl or compute tactics would be too slow if using unary nat,
     but with N and vm_compute, this is instantaneous.
  *)
  vm_compute.
  reflexivity.
Qed.