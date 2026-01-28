Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (1 + 2 * i) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [30; 1; 5; 3; 52; 7; 10; 6; 9; 23; 2; 9] 6.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.