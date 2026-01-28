Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun k => nth (2 * k + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [122; 9; 4; 6; 10; 11; 13; 15; 13] 6.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.