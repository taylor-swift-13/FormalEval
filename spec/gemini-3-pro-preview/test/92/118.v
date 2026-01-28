Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (1437/10) (-20) (-1237/10) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate.
  - intros [H _].
    destruct H as [n Hn].
    apply (f_equal (fun v => v * 10)) in Hn.
    replace ((1437 / 10) * 10) with 1437 in Hn by lra.
    rewrite <- mult_IZR in Hn.
    apply eq_IZR in Hn.
    assert (Hmod: (1437 mod 10 = 0)%Z).
    { rewrite <- Hn. apply Z.mod_mul. lia. }
    vm_compute in Hmod.
    discriminate.
Qed.