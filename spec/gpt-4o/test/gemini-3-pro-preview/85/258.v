Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [1; 3; 5; 12; 7; 9; 920; 12; 15; 18; 920; 920] 962.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.