Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Psatz. (* Needed for lia *)
Open Scope Z_scope.
Open Scope R_scope.

Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* For string conversion to Reals, assume a conversion function exists *)
Parameter string_to_R : string -> R.

Inductive value_of_rel : val -> R -> Prop :=
  | vor_int : forall z, value_of_rel (VInt z) (IZR z)
  | vor_float : forall r, value_of_rel (VFloat r) r
  | vor_str : forall s, value_of_rel (VStr s) (string_to_R s).

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

Example compare_one_test : compare_one_spec (VInt 1) (VFloat 2.5) (Some (VFloat 2.5)).
Proof.
  unfold compare_one_spec.
  left.
  exists (IZR 1), (2.5).
  split.
  - apply vor_int.
  - split.
    + apply vor_float.
    + split.
      * apply rbr_lt. unfold Rlt. unfold IZR. unfold Rlt. lra.
      * reflexivity.
Qed.