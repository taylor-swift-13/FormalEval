Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 42; 13; 14; 15; 19; 18; 19; 10; 4] 80.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.