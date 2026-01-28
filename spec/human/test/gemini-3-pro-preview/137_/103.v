Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.
Open Scope string_scope.

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

Example test_compare_one_10_neg4_1 : compare_one_spec (VInt 10) (VStr "-4,1") (Some (VInt 10)).
Proof.
  unfold compare_one_spec.
  right. left.
  exists (IZR 10), (-(IZR 41 / IZR 10)).
  split.
  - apply vor_int.
  - split.
    + apply vor_str.
    + split.
      * apply rbr_lt.
        apply Rlt_trans with 0.
        -- apply Ropp_lt_gt_0_contravar.
           unfold Rdiv.
           apply Rmult_lt_0_compat.
           ++ apply IZR_lt. reflexivity.
           ++ apply Rinv_0_lt_compat. apply IZR_lt. reflexivity.
        -- apply IZR_lt. reflexivity.
      * reflexivity.
Qed.