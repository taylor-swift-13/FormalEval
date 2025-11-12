
Require Import List.
Require Import ZArith.
Require Import Psatz.

Definition max_fill_spec (grid : list (list Z)) (capacity : Z) (result : Z) : Prop :=
  capacity > 0 /\
  Forall (fun row => length row = length (hd nil grid)) grid /\
  Forall (fun row => Forall (fun x => x = 0 \/ x = 1) row) grid /\
  result = fold_left Z.add (map (fun row => Z.div (Z.add (fold_left Z.add row 0) (Z.sub capacity 1)) capacity) grid) 0.
