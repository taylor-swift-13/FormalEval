Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [16; 44; 16; 4; 6; 26; 11; 13; 15] 74.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.