Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint to_digits_helper (n k : nat) {struct k} : list nat :=
  match k with
  | 0 => []
  | S k' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: to_digits_helper (n / 10) k'
    end
  end.

Definition to_digits_rev (n : nat) : list nat :=
  to_digits_helper n n.

Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => andb (x =? y) (list_nat_eqb t1 t2)
  | _, _ => false
  end.

Definition is_palindrome_b (n : nat) : bool :=
  let d := to_digits_rev n in
  if (n =? 0) then false else list_nat_eqb d (rev d).

Definition is_even (n : nat) : bool :=
  (n mod 2 =? 0).

Definition is_even_pal (n : nat) : bool :=
  andb (is_palindrome_b n) (is_even n).

Definition is_odd_pal (n : nat) : bool :=
  andb (is_palindrome_b n) (negb (is_even n)).

Fixpoint count_in_range (P : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' =>
    (if P (S k') then 1 else 0) +
    count_in_range P k'
  end.

Definition count_palindromes_impl (n : nat) : nat * nat :=
  (count_in_range is_even_pal n, count_in_range is_odd_pal n).

(* n is a positive integer *)
Definition problem_107_pre (n : nat) : Prop := n > 0.

Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  output = count_palindromes_impl n.

Example test_case_107 : problem_107_spec 19 (4, 6).
Proof.
  unfold problem_107_spec.
  vm_compute.
  reflexivity.
Qed.