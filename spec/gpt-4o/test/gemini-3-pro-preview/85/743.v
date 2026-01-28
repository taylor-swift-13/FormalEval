Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (seq 1 ((length lst + 3) / 2)))) 0.

Example test_add_spec : add_spec [1; 2; 3; 4; 5; 42; 7; 7; 9; 10; 11; 12; 13; 14; 67; 15; 16; 17; 18; 19; 20; 1; 10] 84.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.