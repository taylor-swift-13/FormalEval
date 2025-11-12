
Require Import Coq.ZArith.ZArith.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  (x = 1 -> result = true) /\
  (n = 0 -> result = (x =? 0)) /\
  (n = 1 -> result = (x =? 1)) /\
  (n = -1 -> result = (Z.abs x =? 1)) /\
  (n <> 0 /\ n <> 1 /\ n <> -1 ->
    (exists p : Z, p >= 0 /\ Z.pow n p = x) -> result = true /\
    (forall p : Z, p >= 0 -> Z.pow n p <> x) -> result = false).
