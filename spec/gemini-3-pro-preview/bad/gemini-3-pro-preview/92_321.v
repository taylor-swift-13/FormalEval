Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists k : Z, r = IZR k.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (1437/10) (-20) (-12380980628085806/100000000000000) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros (Hx & _).
    unfold is_int in Hx.
    destruct Hx as [k Hk].
    apply (Rmult_eq_compat_r 10) in Hk.
    replace (1437 / 10 * 10) with 1437 in Hk by lra.
    replace 10 with (IZR 10) in Hk by reflexivity.
    rewrite <- mult_IZR in Hk.
    apply eq_IZR_R in Hk.
    assert (Hcontra: (1437 mod 10 = 0)%Z).
    { rewrite Hk. apply Z.mod_mul. lia. }
    vm_compute in Hcontra.
    discriminate Hcontra.
Qed.