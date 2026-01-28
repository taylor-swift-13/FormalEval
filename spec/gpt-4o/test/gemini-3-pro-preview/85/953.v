Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [4; 6; 88; 10; 12; 14; 16; 15; 20; 22; 24; 28; 30; 16; 16; 24] 120.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.