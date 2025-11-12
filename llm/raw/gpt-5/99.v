Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Open Scope R_scope.
Open Scope Z_scope.

Parameter parse_real : string -> R -> Prop.

Definition closest_integer_spec (value : string) (res : Z) : Prop :=
  exists r : R,
    parse_real value r /\
    exists n : Z, exists f : R,
      0 <= f /\ f < 1 /\
      r = IZR n + f /\
      (f < 1/2 -> res = n) /\
      (f > 1/2 -> res = (n + 1)%Z) /\
      (f = 1/2 -> (0 <= r -> res = (n + 1)%Z) /\ (r < 0 -> res = n)).