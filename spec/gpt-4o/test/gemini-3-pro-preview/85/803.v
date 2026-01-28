Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth (2 * i + 1) lst 0) (seq 0 (length lst / 2)))) 0.

Example test_add_spec : add_spec [22; 33; 69; 66; 68; 67; 101; 77; 920; 99; 18; 66; 67] 132.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.