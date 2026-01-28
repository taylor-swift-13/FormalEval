Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (Nat.add (Nat.mul 2 i) 1) lst 0) (seq 0 (Nat.div (length lst) 2)))) 0.

Example test_add_spec : add_spec [3; 5; 100; 55; 98; 7; 9; 12; 6] 12.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.