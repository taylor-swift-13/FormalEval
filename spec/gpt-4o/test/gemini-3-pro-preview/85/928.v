Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (map (fun k => 2 * k + 1) (seq 0 (length lst / 2))))) 0.

Example test_add_spec : add_spec [3; 6; 2; 7; 7; 19; 8; 1; 9; 5; 6] 6.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.