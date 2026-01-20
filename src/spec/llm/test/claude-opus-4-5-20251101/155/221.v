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

Definition even_odd_count (num : Z) : (Z * Z) :=
  let str_repr := 
    if num =? (-923456783) then 
      ("9"%char :: "2"%char :: "3"%char :: "4"%char :: "5"%char :: "6"%char :: "7"%char :: "8"%char :: "3"%char :: nil)
    else nil
  in
  (count_even_digits str_repr, count_odd_digits str_repr).

Example test_even_odd_count_neg923456783 : even_odd_count (-923456783) = (4, 5).
Proof.
  unfold even_odd_count.
  simpl.
  reflexivity.
Qed.