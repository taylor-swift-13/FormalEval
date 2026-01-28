Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Import ListNotations.

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

Parameter val_Z : Z -> Any.
Parameter val_Str : string -> Any.
Parameter val_R : R -> Any.
Parameter mk_int : Z -> int.

Axiom IsInt_Z : forall z, IsInt (val_Z z) (mk_int z).
Axiom Not_IsInt_Str : forall s n, ~ IsInt (val_Str s) n.
Axiom Not_IsInt_R : forall r n, ~ IsInt (val_R r) n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [val_Z 1%Z; val_Z 2%Z; val_Z 3%Z; val_Str "four"; val_R 5.5%R; val_Z 6%Z; val_Str "seven"; val_Str "8"; val_R 9.0%R] 
    [mk_int 1%Z; mk_int 2%Z; mk_int 3%Z; mk_int 6%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply IsInt_Z.
  apply fir_cons_int. apply IsInt_Z.
  apply fir_cons_int. apply IsInt_Z.
  apply fir_cons_nonint. apply Not_IsInt_Str.
  apply fir_cons_nonint. apply Not_IsInt_R.
  apply fir_cons_int. apply IsInt_Z.
  apply fir_cons_nonint. apply Not_IsInt_Str.
  apply fir_cons_nonint. apply Not_IsInt_Str.
  apply fir_cons_nonint. apply Not_IsInt_R.
  apply fir_nil.
Qed.