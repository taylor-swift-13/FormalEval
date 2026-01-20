Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

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

Example test_case : solution_spec [5%Z; 8%Z; 7%Z; 1%Z] 12%Z.
Proof.
  (* Unfold the specification definition *)
  unfold solution_spec.
  (* Unfold the main function definition *)
  unfold sum_odd_at_even_positions.
  (* Simplify the execution of the fixpoint function on the concrete list *)
  simpl.
  (* Verify that the computed value (12) is equal to the expected value (12) *)
  reflexivity.
Qed.