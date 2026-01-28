Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [3; 2; 557; 4; 5; 6; 7; 17; 8; 9; 10; 11; 12; 17; 15; 16; 9; 17; 18; 20; 20; 15] 48.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.