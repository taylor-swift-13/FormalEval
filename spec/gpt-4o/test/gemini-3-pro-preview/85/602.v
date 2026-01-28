Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 8; 2; 557; 4; 5; 6; 43; 17; 8; 3; 10; 11; 12; 17; 15; 16; 10; 17; 18; 20; 20; 15; 20] 106.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.