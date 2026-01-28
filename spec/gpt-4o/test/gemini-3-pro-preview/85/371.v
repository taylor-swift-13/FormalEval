Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [11; 24; 32; 54; 44; 55; 66; 77; 88; 66; 28; 89; 100; 44; 22] 188.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.