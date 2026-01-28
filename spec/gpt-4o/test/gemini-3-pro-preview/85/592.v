Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [1; 2; 28; 4; 5; 6; 7; 8; 9; 6; 10; 11; 12; 12; 13; 6; 15; 16; 17; 18; 19; 20; 10; 8; 13; 18] 124.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.