Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

(* Parameters and axioms to represent mixed types in Any for the test case *)
Parameter inj_Z : Z -> Any.
Parameter inj_Str : string -> Any.
Parameter inj_R : R -> Any.
Parameter inj_Bool : bool -> Any.
Parameter inj_None : Any.

Parameter z2i : Z -> int.

Axiom IsInt_inj_Z : forall z, IsInt (inj_Z z) (z2i z).
Axiom NotInt_inj_Str : forall s n, ~ IsInt (inj_Str s) n.
Axiom NotInt_inj_R : forall r n, ~ IsInt (inj_R r) n.
Axiom NotInt_inj_Bool : forall b n, ~ IsInt (inj_Bool b) n.
Axiom NotInt_inj_None : forall n, ~ IsInt inj_None n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [inj_Str "apple"%string; inj_R (IZR 271828%Z / IZR 100000%Z)%R; inj_None; inj_Bool false; inj_Str "wahellhellootermelon"%string; inj_Z 42%Z] 
    [z2i 42%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply NotInt_inj_Str.
  - apply fir_cons_nonint.
    + apply NotInt_inj_R.
    + apply fir_cons_nonint.
      * apply NotInt_inj_None.
      * apply fir_cons_nonint.
        -- apply NotInt_inj_Bool.
        -- apply fir_cons_nonint.
           ++ apply NotInt_inj_Str.
           ++ apply fir_cons_int.
              ** apply IsInt_inj_Z.
              ** apply fir_nil.
Qed.