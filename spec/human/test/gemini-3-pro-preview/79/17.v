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
 * Since positive is already a binary representation, we can recurse structurally.
 *)
Fixpoint pos_to_binary_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary_string p' ++ "0"
  | xI p' => pos_to_binary_string p' ++ "1"
  end.

(* 
 * @brief Wrapper for the binary conversion for Z.
 * Handles Z0 and Zpos.
 *)
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary_string p
  | _ => "" 
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
  problem_79_spec 1000000001 "db111011100110101100101000000001db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* Use vm_compute for efficient calculation of large integers *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.