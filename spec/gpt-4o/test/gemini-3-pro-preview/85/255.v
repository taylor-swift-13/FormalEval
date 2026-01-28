Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [1; 2; 4; 4; 5; 6; 7; 13; 9; 11; 12; 42; 13; 14; 15; 17; 19; 10] 78.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.