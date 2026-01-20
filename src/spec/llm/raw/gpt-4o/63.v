
Require Import Coq.ZArith.ZArith.

Definition fibfib_spec (n : Z) (result : Z) : Prop :=
  (n = 0 \/ n = 1 -> result = 0) /\
  (n = 2 -> result = 1) /\
  (n >= 3 -> exists a b c, 
    a = 0 /\ b = 0 /\ c = 1 /\
    (forall i, 3 <= i <= n -> 
      let temp := a + b + c in
      a = b /\ b = c /\ c = temp) /\
    result = c).
