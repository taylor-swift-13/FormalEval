
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  let abs_a := Z.abs a in
  result = true <-> exists x : Z, x ^ 3 = abs_a.
