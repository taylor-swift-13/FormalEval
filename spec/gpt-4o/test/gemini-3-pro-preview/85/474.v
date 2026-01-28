Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun k => nth (2 * k + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [3; 5; 7; 9; 2; 6; 3; 8; 10; 556; 100; 30; 920; 42; 37; 29; 555; 23; 8; 100] 742.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.