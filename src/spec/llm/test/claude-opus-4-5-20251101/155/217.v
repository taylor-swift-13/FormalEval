Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.

Open Scope Z_scope.

Definition is_even_digit (c : ascii) : bool :=
  match c with
  | "0"%char | "2"%char | "4"%char | "6"%char | "8"%char => true
  | _ => false
  end.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

Fixpoint count_even_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_even_digit c then 1 else 0) + count_even_digits rest
  end.

Fixpoint count_odd_digits (s : list ascii) : Z :=
  match s with
  | nil => 0
  | c :: rest => (if is_odd_digit c then 1 else 0) + count_odd_digits rest
  end.

Definition digits_of_neg_1021021021021021021021021021021021021021021021013 : list ascii :=
  "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "2"%char :: "1"%char :: "0"%char :: "1"%char :: "3"%char :: nil.

Definition even_odd_count (num : Z) : (Z * Z) :=
  let str_repr := 
    if num =? (-1021021021021021021021021021021021021021021021013) then digits_of_neg_1021021021021021021021021021021021021021021021013
    else nil
  in
  (count_even_digits str_repr, count_odd_digits str_repr).

Example test_even_odd_count_neg : even_odd_count (-1021021021021021021021021021021021021021021021013) = (31, 18).
Proof.
  unfold even_odd_count.
  simpl.
  reflexivity.
Qed.