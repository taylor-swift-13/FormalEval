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
      if (n =? 0) then "0"
      else if (n =? 1) then "1"
      else
        let bit := if Z.even n then "0" else "1" in
        Z_to_binary_string_aux (n / 2) fuel' ++ bit
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  if (n =? 0) then "0"
  else Z_to_binary_string_aux n 256.

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
Example test_decimal_to_binary_1 : problem_79_spec 1000000000009 "db1110100011010100101001010001000000001001db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold Z_to_binary_string.
  vm_compute.
  reflexivity.
Qed.