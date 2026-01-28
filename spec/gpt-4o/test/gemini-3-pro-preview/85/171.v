Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (seq 1 (length lst / 2)))) 0.

Example test_add_spec : add_spec [1; 3; 7; 10; 1; 1] 10.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.