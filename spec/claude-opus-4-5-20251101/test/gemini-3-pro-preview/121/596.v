Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.

Definition is_odd (n : Z) : bool :=
  Z.odd n.

Definition is_even_pos (i : nat) : bool :=
  Nat.even i.

Fixpoint sum_odd_at_even_positions_aux (lst : list Z) (idx : nat) : Z :=
  match lst with
  | nil => 0
  | x :: xs =>
    let rest := sum_odd_at_even_positions_aux xs (S idx) in
    if (is_even_pos idx) && (is_odd x) then x + rest else rest
  end.

Definition sum_odd_at_even_positions (lst : list Z) : Z :=
  sum_odd_at_even_positions_aux lst 0.

Definition solution_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_odd_at_even_positions lst.

Example test_example : solution_spec [3%Z; 3%Z; 4%Z; 4%Z; 6%Z; 9%Z; 75%Z; 12%Z; 8%Z; 11%Z; 34%Z; 8%Z; 3%Z] 81%Z.
Proof.
  unfold solution_spec.
  unfold sum_odd_at_even_positions.
  simpl.
  reflexivity.
Qed.