Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint pos_to_binary (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary p' ++ "0"
  | xI p' => pos_to_binary p' ++ "1"
  end.

Definition nat_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary p
  | Zneg _ => ""
  end.

Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_decimal_to_binary_huge : problem_79_spec 1000000000002 "db1110100011010100101001010001000000000010db".
Proof.
  unfold problem_79_spec.
  vm_compute.
  reflexivity.
Qed.