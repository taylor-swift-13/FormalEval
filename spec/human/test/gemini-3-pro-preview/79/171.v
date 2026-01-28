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
      match n with
      | 0 => "0"
      | 1 => "1"
      | _ =>
          if Z.even n then
            Z_to_binary_string_aux (Z.div2 n) fuel' ++ "0"
          else
            Z_to_binary_string_aux (Z.div2 n) fuel' ++ "1"
      end
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel based on log2 n.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => Z_to_binary_string_aux n (Z.to_nat (Z.log2 n) + 1)
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
Example test_decimal_to_binary_large : problem_79_spec 9223372036854775811 "db1000000000000000000000000000000000000000000000000000000000000011db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  vm_compute.
  reflexivity.
Qed.