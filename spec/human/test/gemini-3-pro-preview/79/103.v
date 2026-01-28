Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert Z to binary string representation.
 * Note: The recursion is bounded by 'fuel' to satisfy Coq's termination checker.
 *)
Fixpoint Z_to_binary_string_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      if Z.eqb n 0 then "0"
      else if Z.eqb n 1 then "1"
      else
          if Z.even n then
            Z_to_binary_string_aux (Z.div n 2) fuel' ++ "0"
          else
            Z_to_binary_string_aux (Z.div (n - 1) 2) fuel' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel based on log2.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_string_aux n (Z.to_nat (Z.log2 n) + 5).

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
Example test_decimal_to_binary_large : problem_79_spec 9223372036854775807 "db111111111111111111111111111111111111111111111111111111111111111db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* Compute the result efficiently *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.