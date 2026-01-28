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
Parameter n1 n8 n9 : int.

Axiom H_v1 : IsInt v1 n1.
Axiom H_v2 : forall n, ~ IsInt v2 n.
Axiom H_v3 : forall n, ~ IsInt v3 n.
Axiom H_v4 : forall n, ~ IsInt v4 n.
Axiom H_v5 : forall n, ~ IsInt v5 n.
Axiom H_v6 : forall n, ~ IsInt v6 n.
Axiom H_v7 : forall n, ~ IsInt v7 n.
Axiom H_v8 : IsInt v8 n8.
Axiom H_v9 : IsInt v9 n9.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [n1; n8; n9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. exact H_v1.
  apply fir_cons_nonint. exact H_v2.
  apply fir_cons_nonint. exact H_v3.
  apply fir_cons_nonint. exact H_v4.
  apply fir_cons_nonint. exact H_v5.
  apply fir_cons_nonint. exact H_v6.
  apply fir_cons_nonint. exact H_v7.
  apply fir_cons_int. exact H_v8.
  apply fir_cons_int. exact H_v9.
  apply fir_nil.
Qed.