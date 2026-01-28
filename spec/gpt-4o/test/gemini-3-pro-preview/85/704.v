Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (map (fun k => 2 * k + 1) (seq 0 (length lst / 2))))) 0.

Example test_add_spec : add_spec [3; 5; 7; 9; 2; 122; 6; 7; 10; 556; 100; 187; 920; 42; 37; 122; 29] 842.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.