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
Fixpoint nat_to_binary_string_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | 0 => "0"
      | 1 => "1"
      | _ =>
          if Z.even n then
            nat_to_binary_string_aux (Z.div n 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux (Z.div n 2) fuel' ++ "1"
      end
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel based on log2.
 *)
Definition nat_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => nat_to_binary_string_aux n (S (Z.to_nat (Z.log2 n)))
  end.

(* 
 * @brief Main implementation matching the specification.
 * Adds "db" prefix and suffix.
 *)
Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

(* Test case verification *)
Example test_decimal_to_binary_1000000004 : problem_79_spec 1000000004 "db111011100110101100101000000100db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* Unfold the inner conversion function *)
  unfold nat_to_binary_string.
  
  (* 
     Simplify the expression. 
     Using vm_compute to handle integer arithmetic efficiently.
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.