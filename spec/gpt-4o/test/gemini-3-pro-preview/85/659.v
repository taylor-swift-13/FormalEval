Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (Nat.div (length lst) 2)))) 0.

Example test_add_spec : add_spec [1; 4; 3; 8; 16; 7; 10; 14; 1; 16; 1] 42.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.