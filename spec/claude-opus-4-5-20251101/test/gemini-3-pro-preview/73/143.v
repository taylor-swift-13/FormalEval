Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.

Import ListNotations.

Open Scope Z_scope.

Definition is_palindrome (arr : list Z) : Prop :=
  arr = rev arr.

Fixpoint count_mismatches (l1 l2 : list Z) (n : nat) : nat :=
  match n with
  | O => O
  | S n' =>
    match l1, l2 with
    | x :: xs, y :: ys =>
      if Z.eqb x y then count_mismatches xs ys n'
      else S (count_mismatches xs ys n')
    | _, _ => O
    end
  end.

Definition smallest_change_spec (arr : list Z) (result : nat) : Prop :=
  let arr_reversed := rev arr in
  let half_len := (length arr / 2)%nat in
  result = count_mismatches arr arr_reversed half_len.

Example test_smallest_change : smallest_change_spec [1%Z; 2%Z; 46%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 7%Z; 10%Z; 10%Z; 9%Z; 8%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 10%Z] 4%nat.
Proof.
  unfold smallest_change_spec.
  simpl.
  reflexivity.
Qed.