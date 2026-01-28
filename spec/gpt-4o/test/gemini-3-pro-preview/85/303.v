Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 22; 1; 6; 7; 4; 8; 1; 9; 9; 5; 23; 8; 1] 32.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.