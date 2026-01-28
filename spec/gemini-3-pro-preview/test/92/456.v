Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (
    (exists i : Z, IZR i = x) /\
    (exists i : Z, IZR i = y) /\
    (exists i : Z, IZR i = z) /\
    (x = y + z \/ y = x + z \/ z = x + y)
  ).

Example test_any_int : any_int_spec (-63.92630339077474) (-123.7) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros (_ & _ & _ & H).
    lra.
Qed.