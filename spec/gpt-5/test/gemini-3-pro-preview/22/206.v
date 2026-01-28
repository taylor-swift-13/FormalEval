Require Import Coq.Lists.List.
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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameter i1 i2 i4 : int.

Axiom IsInt_v1 : IsInt v1 i1.
Axiom IsInt_v2 : IsInt v2 i2.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom IsInt_v4 : IsInt v4 i4.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom NotInt_v6 : forall n, ~ IsInt v6 n.
Axiom NotInt_v7 : forall n, ~ IsInt v7 n.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.
Axiom NotInt_v9 : forall n, ~ IsInt v9 n.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [i1; i2; i4].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := i1). apply IsInt_v1.
  apply fir_cons_int with (n := i2). apply IsInt_v2.
  apply fir_cons_nonint. apply NotInt_v3.
  apply fir_cons_int with (n := i4). apply IsInt_v4.
  apply fir_cons_nonint. apply NotInt_v5.
  apply fir_cons_nonint. apply NotInt_v6.
  apply fir_cons_nonint. apply NotInt_v7.
  apply fir_cons_nonint. apply NotInt_v8.
  apply fir_cons_nonint. apply NotInt_v9.
  apply fir_nil.
Qed.