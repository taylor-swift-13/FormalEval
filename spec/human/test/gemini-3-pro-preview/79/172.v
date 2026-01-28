Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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
      if n =? 0 then "0"
      else if n =? 1 then "1"
      else
          if Z.even n then
            Z_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            Z_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and calculates sufficient fuel.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => Z_to_binary_string_aux n (S (Z.to_nat (Z.log2 n)))
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
Example test_decimal_to_binary_large : problem_79_spec 9999999999999999999999999999997 "db1111110001101111011111000100000001000101100000010010001010010110010011001111111111111111111111111111101db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold Z_to_binary_string.
  vm_compute.
  reflexivity.
Qed.