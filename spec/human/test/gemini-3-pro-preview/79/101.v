Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint Z_to_binary_string_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      if n =? 0 then "0"
      else if n =? 1 then "1"
      else
        let remainder := if Z.even n then "0" else "1" in
        Z_to_binary_string_aux (n / 2) fuel' ++ remainder
  end.

Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => Z_to_binary_string_aux n 100%nat
  end.

Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ Z_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_decimal_to_binary_large : problem_79_spec 999999993 "db111011100110101100100111111001db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  vm_compute.
  reflexivity.
Qed.