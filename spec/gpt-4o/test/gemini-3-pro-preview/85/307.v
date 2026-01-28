Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [11; 33; 54; 44; 55; 66; 77; 88; 66; 100; 44; 33; 100] 298.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.