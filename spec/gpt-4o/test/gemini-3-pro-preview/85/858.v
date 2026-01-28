Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i - 1) lst 0) (seq 1 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 6; 2; 7; 8; 6; 920; 9; 10] 12.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.