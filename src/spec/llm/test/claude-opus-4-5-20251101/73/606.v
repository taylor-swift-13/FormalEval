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

Example test_smallest_change :
  smallest_change_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 13%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z] 25%nat.
Proof.
  unfold smallest_change_spec.
  simpl.
  reflexivity.
Qed.