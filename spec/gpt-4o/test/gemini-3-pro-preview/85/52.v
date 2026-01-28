Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (map (fun k => 1 + 2 * k) (seq 0 (length lst / 2))))) 0.

Example test_add_spec : add_spec [1; 2; 2; 4; 3; 5; 2; 1; 3] 6.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.