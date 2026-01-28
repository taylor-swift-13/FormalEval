Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (map (fun k => 2 * k + 1) (seq 0 (length lst / 2))))) 0.

Example test_add_spec : add_spec [1; 4; 3; 8; 16; 7; 10; 14; 16; 7; 16; 8] 34.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.