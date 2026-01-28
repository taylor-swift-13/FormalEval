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
 * Recursion is structural on positive.
 *)
Fixpoint pos_to_binary_string (p : positive) : string :=
  match p with
  | xI p' => pos_to_binary_string p' ++ "1"
  | xO p' => pos_to_binary_string p' ++ "0"
  | xH => "1"
  end.

(* 
 * @brief Wrapper for the binary conversion.
 * Handles 0 explicitly and uses Z.
 *)
Definition nat_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary_string p
  | Zneg p => "" (* Assumes non-negative input *)
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
Example test_decimal_to_binary_large : problem_79_spec 9999999999999999999999999999995 "db1111110001101111011111000100000001000101100000010010001010010110010011001111111111111111111111111111011db".
Proof.
  (* Unfold the specification definition *)
  unfold problem_79_spec.
  
  (* Unfold the implementation definition *)
  unfold decimal_to_binary_impl.
  
  (* Unfold the inner conversion function *)
  unfold nat_to_binary_string.
  
  (* 
     Simplify the expression. 
     Computation is performed on Z (binary integers).
  *)
  vm_compute.
  
  (* Verify equality *)
  reflexivity.
Qed.