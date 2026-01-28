Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (res : bool) : Prop :=
  res = true <-> (x = y + z \/ y = x + z \/ z = x + y).

Example test_any_int : any_int_spec 3 3 2 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    lia.
Qed.