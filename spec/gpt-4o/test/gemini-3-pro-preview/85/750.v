Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [78; 11; 22; 33; 66; 68; 67; 77; 98; 100] 168.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.