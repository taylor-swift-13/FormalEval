Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint Z_to_binary_string_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | 0 => "0"
      | 1 => "1"
      | _ =>
          if Z.even n then
            Z_to_binary_string_aux (Z.div n 2) fuel' ++ "0"
          else
            Z_to_binary_string_aux (Z.div n 2) fuel' ++ "1"
      end
  end.

Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | 0 => "0"
  | _ => Z_to_binary_string_aux n (Z.to_nat (Z.log2 n) + 2)
  end.

Definition decimal_to_binary_impl (decimal : Z) : string :=
  "db" ++ Z_to_binary_string decimal ++ "db".
  
Definition problem_79_pre (decimal : Z) : Prop := True.

Definition problem_79_spec (decimal : Z) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_decimal_to_binary_huge : problem_79_spec 9999999999999999999999999999999 "db1111110001101111011111000100000001000101100000010010001010010110010011001111111111111111111111111111111db".
Proof.
  unfold problem_79_spec.
  vm_compute.
  reflexivity.
Qed.