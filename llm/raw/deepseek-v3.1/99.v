
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

Definition closest_integer_spec (value : string) (result : Z) : Prop :=
  exists r : R,
    r = IZR (Z.of_string value) /\
    (Rabs (r - IZR (Zfloor r)) <> 1/2 -> result = ZnearestE r) /\
    (Rabs (r - IZR (Zfloor r)) = 1/2 -> 
     (r > 0 -> result = Zfloor r + 1) /\
     (r < 0 -> result = Zfloor r - 1) /\
     (r = 0 -> result = 0)).
