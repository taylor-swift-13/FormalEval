Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint pos_to_binary_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => pos_to_binary_string p' ++ "0"
  | xI p' => pos_to_binary_string p' ++ "1"
  end.

Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary_string p
  | Zneg _ => ""
  end.

Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ Z_to_binary_string decimal ++ "db".

Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_decimal_to_binary_huge : problem_79_spec 10000000000000000000000000000001 "db1111110001101111011111000100000001000101100000010010001010010110010011010000000000000000000000000000001db".
Proof.
  vm_compute.
  reflexivity.
Qed.