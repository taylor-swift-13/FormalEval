
Require Import List.
Require Import ZArith.
Import ListNotations.

Definition will_it_fly_spec (q : list Z) (w : Z) (result : bool) : Prop :=
  result = (q =? rev q) && (Z.leb (fold_right Z.add 0 q) w).
