Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope string_scope.

(* 
 * @brief Helper function to convert nat to binary string representation.
 * Note: The recursion is bounded by 'fuel' to satisfy Coq's termination checker.
 *)
Fixpoint nat_to_binary_string_aux (n fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => "0"
      | 1 => "1"
      | _ =>
          if Nat.even n then
            nat_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
      end
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel equal to n.
 *)
Definition nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | _ => nat_to_binary_string_aux n n
  end.

(* 
 * @brief Main implementation matching the specification.
 * Adds "db" prefix and suffix.
 *)
Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

(* Test case verification *)
Example test_decimal_to_binary_2 : problem_79_spec 2 "db10db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold nat_to_binary_string.
  vm_compute.
  reflexivity.
Qed.