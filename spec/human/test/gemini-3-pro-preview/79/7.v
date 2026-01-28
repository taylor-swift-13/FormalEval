Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* 
 * @brief Helper function to convert positive to binary string representation.
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
  | Zneg _ => ""
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
Example test_decimal_to_binary_1 : problem_79_spec 999999999 "db111011100110101100100111111111db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold Z_to_binary_string.
  vm_compute.
  reflexivity.
Qed.