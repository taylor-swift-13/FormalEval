Require Import List.
Require Import Nat.
Import ListNotations.

Definition add_spec (lst : list nat) (s : nat) : Prop :=
  s = fold_left Nat.add (filter (fun x => Nat.even x) (map (fun i => nth i lst 0) (filter Nat.odd (seq 0 (length lst))))) 0.

Example test_add_spec : add_spec [2; 6; 13; 187; 8; 10; 12; 14; 17; 18; 20; 22; 26; 24; 26; 28; 30] 122.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.