Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [8; 122; 9; 4; 6; 10; 13; 15; 9] 136.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.