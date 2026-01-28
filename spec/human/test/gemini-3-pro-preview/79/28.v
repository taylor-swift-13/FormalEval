Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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
          Z_to_binary_string_aux (Z.div n 2) fuel' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and sets initial fuel based on log2.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => Z_to_binary_string_aux n (Nat.add (Z.to_nat (Z.log2 n)) 2)
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
Example test_decimal_to_binary_large : problem_79_spec 999999998 "db111011100110101100100111111110db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* 
     Use vm_compute for efficient computation with Z integers.
     Standard simpl or compute would timeout on large numbers if represented as Peano nats.
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.