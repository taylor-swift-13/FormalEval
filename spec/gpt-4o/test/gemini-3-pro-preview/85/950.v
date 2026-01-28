Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter Nat.even (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [11; 8; 30; 66; 67; 77; 88; 77; 99; 100; 77; 76; 100; 66; 66] 316.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.