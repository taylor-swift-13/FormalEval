Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition is_even (n : Z) : bool :=
  Z.eqb (Z.modulo n 2) 0.

Definition is_odd_index (i : nat) : bool :=
  Nat.odd i.

Fixpoint add_even_at_odd_indices_aux (lst : list Z) (idx : nat) : Z :=
  match lst with
  | [] => 0
  | x :: xs =>
    let rest := add_even_at_odd_indices_aux xs (S idx) in
    if andb (is_odd_index idx) (is_even x) then x + rest else rest
  end.

Definition add_even_at_odd_indices (lst : list Z) : Z :=
  add_even_at_odd_indices_aux lst 0.

Definition add_spec (lst : list Z) (result : Z) : Prop :=
  result = add_even_at_odd_indices lst.

Example test_add_even_at_odd_indices : add_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 22%Z; 24%Z; 26%Z; 28%Z; 30%Z] 112%Z.
Proof.
  unfold add_spec.
  unfold add_even_at_odd_indices.
  simpl.
  reflexivity.
Qed.