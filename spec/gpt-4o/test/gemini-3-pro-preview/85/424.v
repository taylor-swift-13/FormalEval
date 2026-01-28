Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [1; 3; 5; 7; 9; 11; 13; 2; 4; 6; 8; 8; 10; 12; 14; 8] 36.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.