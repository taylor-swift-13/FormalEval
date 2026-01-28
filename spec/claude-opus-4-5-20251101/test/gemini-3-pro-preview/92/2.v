Require Import ZArith.
Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> 
  ((exists (ix : Z), IZR ix = x) /\ 
   (exists (iy : Z), IZR iy = y) /\ 
   (exists (iz : Z), IZR iz = z) /\ 
   (x = y + z \/ y = x + z \/ z = y + x)).

Example test_any_int : any_int_spec 2.5 2 3 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros (H25 & _).
    destruct H25 as [n Hn].
    assert (2 < n < 3)%Z.
    {
      split; apply lt_IZR; rewrite Hn; lra.
    }
    lia.
Qed.