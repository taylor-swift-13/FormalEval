Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (seq 1 (length lst / 2)))) 0.

Example test_case : add_spec [4; 88] 88.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.