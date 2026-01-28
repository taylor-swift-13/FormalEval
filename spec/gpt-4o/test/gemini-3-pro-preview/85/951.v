Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [2; 4; 6; 17; 10; 8; 10; 14; 16; 18; 20; 17; 23; 13; 28; 30; 6; 23; 10; 15] 74.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.