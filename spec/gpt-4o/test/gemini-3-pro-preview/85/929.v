Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (Nat.div (length lst) 2)))) 0.

Example test_add_spec : add_spec [11; 8; 33; 33; 66; 67; 77; 88; 99; 100; 7; 76; 100; 66; 7] 338.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.