Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [3; 1; 2; 3; 4; 5; 6; 7; 18; 8; 9; 10; 11; 13; 14; 15; 17; 18; 19; 20] 56.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.