Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope Z_scope.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  if result then
    exists (zx zy zz : Z),
      IZR zx = x /\ IZR zy = y /\ IZR zz = z /\
      ((zx = zy + zz)%Z \/ (zy = zx + zz)%Z \/ (zz = zx + zy)%Z)
  else
    ~ (exists (zx zy zz : Z),
      IZR zx = x /\ IZR zy = y /\ IZR zz = z /\
      ((zx = zy + zz)%Z \/ (zy = zx + zz)%Z \/ (zz = zx + zy)%Z)).

Example test_any_int : any_int_spec 2.2 2.2 2.2 false.
Proof.
  unfold any_int_spec.
  intros [zx [zy [zz [Hx [Hy [Hz H]]]]]].
  apply (f_equal (fun r => r * 10)) in Hx.
  replace (2.2 * 10) with 22 in Hx by lra.
  rewrite <- mult_IZR in Hx.
  replace 22 with (IZR 22) in Hx by reflexivity.
  apply eq_IZR in Hx.
  assert (Hmod: (zx * 10) mod 10 = 22 mod 10).
  { rewrite Hx. reflexivity. }
  rewrite Z.mod_mul in Hmod; try lia.
  simpl in Hmod.
  discriminate.
Qed.