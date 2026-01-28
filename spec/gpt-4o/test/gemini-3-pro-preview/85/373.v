Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun k => nth (2 * k + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 5; 7; 9; 2; 6; 187; 10; 20; 556; 3; 187; 12; 42; 37; 30; 7; 8; 187; 7] 652.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.