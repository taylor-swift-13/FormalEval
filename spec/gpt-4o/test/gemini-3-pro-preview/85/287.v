Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (seq 1 (length lst / 2)))) 0.

Example test_add_spec : add_spec [6; 4; 5; 10; 11; 15; 6] 14.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.