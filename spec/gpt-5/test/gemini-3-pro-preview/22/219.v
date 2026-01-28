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

Parameter v1 v2 v3 v4 v5 : Any.

Axiom not_int_v1 : forall n, ~ IsInt v1 n.
Axiom not_int_v2 : forall n, ~ IsInt v2 n.
Axiom not_int_v3 : forall n, ~ IsInt v3 n.
Axiom not_int_v4 : forall n, ~ IsInt v4 n.
Axiom not_int_v5 : forall n, ~ IsInt v5 n.

Example test_filter_integers_lists : 
  filter_integers_spec [v1; v2; v1; v3; v4; v5; v3; v3] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_v1.
  apply fir_cons_nonint. apply not_int_v2.
  apply fir_cons_nonint. apply not_int_v1.
  apply fir_cons_nonint. apply not_int_v3.
  apply fir_cons_nonint. apply not_int_v4.
  apply fir_cons_nonint. apply not_int_v5.
  apply fir_cons_nonint. apply not_int_v3.
  apply fir_cons_nonint. apply not_int_v3.
  apply fir_nil.
Qed.