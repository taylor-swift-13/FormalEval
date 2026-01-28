Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter (fun i => Nat.odd i) (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [2; 4; 55; 88; 10; 12; 14; 16; 18; 20; 22; 24; 28; 30; 16; 28] 222.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.