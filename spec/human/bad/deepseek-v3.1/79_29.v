Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint nat_to_binary_string_aux (n : N) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match N.eqb n 0 with
      | true => "0"
      | false =>
          if N.even n then
            nat_to_binary_string_aux (N.div2 n) fuel' ++ "0"
          else
            nat_to_binary_string_aux (N.pred (N.div2 n)) fuel' ++ "1"
      end
  end.

Definition nat_to_binary_string (n : N) : string :=
  match n with
  | 0 => "0"
  | _ => nat_to_binary_string_aux n (N.size_nat n)
  end.

Definition decimal_to_binary_impl (decimal : N) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".

Definition problem_79_pre (decimal : N) : Prop := True.

Definition problem_79_spec (decimal : N) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_case_0 : problem_79_spec 0 "db0db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold nat_to_binary_string.
  simpl.
  reflexivity.
Qed.

Example test_case_1 : problem_79_spec 999999999999 "db1110100011010100101001010000111111111111db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold nat_to_binary_string.
  simpl.
  reflexivity.
Qed.