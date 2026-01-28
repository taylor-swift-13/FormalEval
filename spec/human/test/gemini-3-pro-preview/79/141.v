Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert positive to binary string representation.
 * Recursively constructs the string by appending "0" or "1".
 *)
Fixpoint pos_to_binary_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary_string p' ++ "0"
  | xI p' => pos_to_binary_string p' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and delegates positive numbers to helper.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary_string p
  | Zneg _ => "" (* Undefined for negative inputs in this context *)
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
Example test_decimal_to_binary_large : 
  problem_79_spec 274877906946 "db100000000000000000000000000000000000010db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* 
     Compute the result. 
     Using vm_compute is efficient for large integer arithmetic and string construction.
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.