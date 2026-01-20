Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f' =>
      if Nat.eqb n 0 then ""
      else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

Definition solve_spec (N : nat) (output : string) : Prop :=
  (N <= 10000) ->
  (output = nat_to_binary_string (sum_decimal_digits N)).

Example solve_test_2230 :
  solve_spec 2230 "111".
Proof.
  unfold solve_spec.
  intros H.
  unfold nat_to_binary_string, sum_decimal_digits.
  simpl.
  reflexivity.
Qed.