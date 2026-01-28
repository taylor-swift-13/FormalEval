Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [2; 4; 6; 8; 10; 12; 14; 16; 18; 37; 22; 37; 24; 26; 28; 30; 16; 18] 114.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.