Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Fixpoint nat_to_binary_string_aux (n fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => "0"
      | 1 => "1"
      | _ =>
          if Nat.even n then
            nat_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
      end
  end.

Definition nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | _ => nat_to_binary_string_aux n n
  end.

Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".

Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_case_4 : problem_79_spec 4 "db100db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold nat_to_binary_string.
  unfold nat_to_binary_string_aux.
  reflexivity.
Qed.