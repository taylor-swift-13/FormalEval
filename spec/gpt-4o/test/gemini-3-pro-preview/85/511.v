Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [3; 5; 7; 9; 2; 6; 3; 8; 10; 556; 100; 187; 42; 37; 29; 44; 8; 187] 614.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.