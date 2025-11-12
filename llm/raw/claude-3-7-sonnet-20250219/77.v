
Require Import ZArith.
Open Scope Z_scope.

Definition iscube_spec (a : Z) (res : bool) : Prop :=
  let a_abs := Z.abs a in
  let c := Z.pow (Z.round (Z.to_real a_abs ** (/3))) 3 in
  res = Bool.eqb c a_abs.
