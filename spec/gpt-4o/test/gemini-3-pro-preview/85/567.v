Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (map (fun k => 1 + 2 * k) (seq 0 (length lst / 2))))) 0.

Example test_add_spec : add_spec [3; 1; 2; 3; 4; 5; 67; 6; 7; 8; 9; 10; 11; 12; 17; 14; 15; 16; 9; 17; 18; 20; 20; 15; 16] 86.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.