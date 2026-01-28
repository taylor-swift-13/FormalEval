Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [2; 6; 11; 17; 8; 8; 10; 12; 14; 16; 18; 20; 17; 54; 24; 13; 28; 29; 6] 116.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.