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

Example test_example : solution_spec [12%Z; 22%Z; 34%Z; 86%Z; 55%Z; 44%Z; 32%Z; 76%Z; 99%Z; 77%Z; 77%Z] 231%Z.
Proof.
  unfold solution_spec.
  unfold sum_odd_at_even_positions.
  simpl.
  reflexivity.
Qed.