Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* 三种输入类型 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

Inductive value_of_rel : val -> R -> Prop :=
  | vor_int : forall z, value_of_rel (VInt z) (IZR z)
  | vor_float : forall r, value_of_rel (VFloat r) r
  | vor_str : forall s r, value_of_rel (VStr s) r.

Inductive Rlt_bool_rel : R -> R -> bool -> Prop :=
  | rbr_lt : forall x y, Rlt x y -> Rlt_bool_rel x y true
  | rbr_ge : forall x y, ~ Rlt x y -> Rlt_bool_rel x y false.


Definition compare_one_spec (a b : val) (res : option val) : Prop :=
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb true /\
     res = Some b) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel rb ra true /\
     res = Some a) \/
  (exists ra rb,
     value_of_rel a ra /\
     value_of_rel b rb /\
     Rlt_bool_rel ra rb false /\
     Rlt_bool_rel rb ra false /\
     res = None).

Example test_compare_one_float : compare_one_spec (VFloat (-1.123543564552395)) (VFloat 2.5) (Some (VFloat 2.5)).
Proof.
  unfold compare_one_spec.
  left.
  exists (-1.123543564552395)%R, 2.5%R.
  split.
  - apply vor_float.
  - split.
    + apply vor_float.
    + split.
      * apply rbr_lt.
        lra.
      * reflexivity.
Qed.