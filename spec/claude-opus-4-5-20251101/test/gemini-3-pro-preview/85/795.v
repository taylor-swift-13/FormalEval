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

Example test_add_even_at_odd_indices : 
  add_spec [2; 4; 6; 17; 10; 8; 10; 14; 16; 18; 20; 17; 23; 13; 28; 30; 6; 23; 10; 14] 88.
Proof.
  unfold add_spec.
  unfold add_even_at_odd_indices.
  compute.
  reflexivity.
Qed.