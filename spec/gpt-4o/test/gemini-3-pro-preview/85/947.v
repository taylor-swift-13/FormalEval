Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (Nat.sub (Nat.mul 2 i) 1) lst 0) (seq 1 (length lst / 2)))) 0.

Example test_add_spec : add_spec [1; 2; 3; 4; 5; 42; 7; 7; 556; 42; 10; 11; 12; 13; 14; 15; 16; 17; 31; 19; 20; 42] 132.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.