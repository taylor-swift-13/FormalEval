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

Example test_add_even_at_odd_indices : add_spec [22%Z; 33%Z; 69%Z; 66%Z; 68%Z; 67%Z; 101%Z; 77%Z; 920%Z; 99%Z; 18%Z; 66%Z; 67%Z] 132%Z.
Proof.
  unfold add_spec.
  unfold add_even_at_odd_indices.
  simpl.
  reflexivity.
Qed.