Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 7; 9; 2; 6; 8; 10; 26; 556; 100; 187; 19; 42; 37; 29; 7; 8; 6; 100; 2] 144.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.