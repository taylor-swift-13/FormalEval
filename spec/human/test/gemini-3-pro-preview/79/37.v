Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert positive to binary string.
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
Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary p
  | Zneg p => pos_to_binary p 
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
  problem_79_spec 1000000000005 "db1110100011010100101001010001000000000101db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* Unfold the inner conversion function *)
  unfold Z_to_binary_string.
  
  (* Verify equality *)
  reflexivity.
Qed.