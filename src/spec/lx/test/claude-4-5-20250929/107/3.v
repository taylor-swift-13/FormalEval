Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Fixpoint to_digits_helper (n k : nat) {struct k} : list nat :=
  match k with
  | O => []
  | S k' =>
      match n with
      | O => []
      | S _ => (n mod 10) :: to_digits_helper (n / 10) k'
      end
  end.

Definition to_digits_rev (n : nat) : list nat :=
  to_digits_helper n n.

Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1 :: t1, h2 :: t2 => andb (h1 =? h2) (list_nat_eqb t1 t2)
  | _, _ => false
  end.

Definition is_palindrome (n : nat) : bool :=
  let digits_rev := to_digits_rev n in
  if (n =? 0)
  then false
  else list_nat_eqb digits_rev (rev digits_rev).

Definition is_even (n : nat) : bool :=
  (n mod 2 =? 0).

Definition is_even_palindrome (n : nat) : bool :=
  andb (is_palindrome n) (is_even n).

Definition is_odd_palindrome (n : nat) : bool :=
  andb (is_palindrome n) (negb (is_even n)).

Fixpoint count_in_range (P : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => (if P (S k') then 1 else 0) + count_in_range P k'
  end.

Definition count_palindromes_spec (n : nat) (res : nat * nat) : Prop :=
  res = (count_in_range is_even_palindrome n, count_in_range is_odd_palindrome n).

Example test_count_palindromes :
  count_palindromes_spec 3 (1, 2).
Proof.
  unfold count_palindromes_spec.
  simpl.
  reflexivity.
Qed.