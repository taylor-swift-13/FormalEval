
Require Import List ZArith.
Import ListNotations.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i, 0 <= i < length l - 1 -> nth i l 0 <= nth (i + 1) l 0) \/
    (forall i, 0 <= i < length l - 1 -> nth i l 0 >= nth (i + 1) l 0).
