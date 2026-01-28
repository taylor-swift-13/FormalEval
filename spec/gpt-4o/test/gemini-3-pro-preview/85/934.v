Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [11; 22; 101; 10; 44; 55; 88; 21; 7; 77; 88; 100; 7] 132.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.