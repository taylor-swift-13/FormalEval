Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> 
  (is_int x /\ is_int y /\ is_int z /\ 
   (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec 2.5 2 3 false.
Proof.
  unfold any_int_spec.
  split.
  - intro H. discriminate H.
  - intro H. intro C.
    destruct C as [Hx _].
    unfold is_int in Hx. destruct Hx as [k Hk].
    replace 2.5 with (5/2) in Hk by field.
    apply (Rmult_eq_compat_l 2) in Hk.
    replace (2 * (5 / 2)) with 5 in Hk by field.
    rewrite <- mult_IZR in Hk.
    apply IZR_eq in Hk.
    assert (Hodd: Z.odd (2 * k) = Z.odd 5).
    { rewrite Hk. reflexivity. }
    simpl in Hodd.
    discriminate Hodd.
Qed.