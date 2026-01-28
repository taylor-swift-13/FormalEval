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

Parameter v_list_5 : Any.
Parameter v_int_7 : Any.
Parameter v_list_mixed : Any.
Parameter n_7 : int.

Axiom not_int_list_5 : forall n, ~ IsInt v_list_5 n.
Axiom is_int_7 : IsInt v_int_7 n_7.
Axiom not_int_list_mixed : forall n, ~ IsInt v_list_mixed n.

Example test_filter_integers_complex : 
  filter_integers_spec [v_list_5; v_list_5; v_int_7; v_list_mixed] [n_7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_list_5.
  apply fir_cons_nonint. apply not_int_list_5.
  apply fir_cons_int with (n := n_7). apply is_int_7.
  apply fir_cons_nonint. apply not_int_list_mixed.
  apply fir_nil.
Qed.