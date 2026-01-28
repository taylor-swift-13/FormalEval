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

Parameter v_2_5 : Any.
Parameter v_4_6 : Any.
Parameter v_7_8 : Any.
Parameter v_abc : Any.
Parameter v_empty_dict : Any.
Parameter v_empty_list : Any.

Axiom not_int_2_5 : forall n, ~ IsInt v_2_5 n.
Axiom not_int_4_6 : forall n, ~ IsInt v_4_6 n.
Axiom not_int_7_8 : forall n, ~ IsInt v_7_8 n.
Axiom not_int_abc : forall n, ~ IsInt v_abc n.
Axiom not_int_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom not_int_empty_list : forall n, ~ IsInt v_empty_list n.

Example test_filter_integers_mixed : filter_integers_spec [v_2_5; v_4_6; v_7_8; v_abc; v_empty_dict; v_empty_list; v_7_8] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_2_5.
  apply fir_cons_nonint. apply not_int_4_6.
  apply fir_cons_nonint. apply not_int_7_8.
  apply fir_cons_nonint. apply not_int_abc.
  apply fir_cons_nonint. apply not_int_empty_dict.
  apply fir_cons_nonint. apply not_int_empty_list.
  apply fir_cons_nonint. apply not_int_7_8.
  apply fir_nil.
Qed.