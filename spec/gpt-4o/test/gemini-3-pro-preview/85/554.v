Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter (fun i => Nat.odd i) (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [5; 3; 8; 7; 10; 6; 9; 24] 30.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.