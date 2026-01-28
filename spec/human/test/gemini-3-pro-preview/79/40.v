Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

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

Example test_decimal_to_binary_large : problem_79_spec 1000000000006 "db1110100011010100101001010001000000000110db".
Proof.
  vm_compute.
  reflexivity.
Qed.