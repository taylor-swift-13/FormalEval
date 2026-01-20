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

Example test_add_even_at_odd_indices : add_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 3%Z; 8%Z; 10%Z; 556%Z; 100%Z; 187%Z; 42%Z; 37%Z; 29%Z; 7%Z; 8%Z] 570%Z.
Proof.
  unfold add_spec.
  unfold add_even_at_odd_indices.
  simpl.
  reflexivity.
Qed.