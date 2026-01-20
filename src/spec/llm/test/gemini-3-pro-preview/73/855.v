Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_diffs (l1 l2 : list Z) : Z :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => (if Z.eq_dec x y then 0 else 1) + count_diffs xs ys
  end.

Definition smallest_change_spec (arr : list Z) (cnt : Z) : Prop :=
  let half_len := Nat.div (length arr) 2 in
  let prefix := firstn half_len arr in
  let suffix_reversed := firstn half_len (rev arr) in
  cnt = count_diffs prefix suffix_reversed.

Example test_smallest_change: 
  smallest_change_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 23%Z; 26%Z; 27%Z; 28%Z; 13%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z; 39%Z] 25%Z.
Proof.
  unfold smallest_change_spec.
  simpl.
  reflexivity.
Qed.