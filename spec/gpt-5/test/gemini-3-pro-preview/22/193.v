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

Parameter v_1 : Any.
Parameter i_1 : int.
Axiom is_int_v_1 : IsInt v_1 i_1.

Parameter v_list_2_3 : Any.
Axiom not_int_v_list_2_3 : forall n, ~ IsInt v_list_2_3 n.

Parameter v_4 : Any.
Parameter i_4 : int.
Axiom is_int_v_4 : IsInt v_4 i_4.

Parameter v_list_5 : Any.
Axiom not_int_v_list_5 : forall n, ~ IsInt v_list_5 n.

Parameter v_nil : Any.
Axiom not_int_v_nil : forall n, ~ IsInt v_nil n.

Parameter v_list_mixed : Any.
Axiom not_int_v_list_mixed : forall n, ~ IsInt v_list_mixed n.

Parameter v_dict : Any.
Axiom not_int_v_dict : forall n, ~ IsInt v_dict n.

Parameter v_str_9 : Any.
Axiom not_int_v_str_9 : forall n, ~ IsInt v_str_9 n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v_1; v_list_2_3; v_4; v_list_5; v_nil; v_1; v_list_mixed; v_dict; v_str_9] 
    [i_1; i_4; i_1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_v_1.
  apply fir_cons_nonint. apply not_int_v_list_2_3.
  apply fir_cons_int. apply is_int_v_4.
  apply fir_cons_nonint. apply not_int_v_list_5.
  apply fir_cons_nonint. apply not_int_v_nil.
  apply fir_cons_int. apply is_int_v_1.
  apply fir_cons_nonint. apply not_int_v_list_mixed.
  apply fir_cons_nonint. apply not_int_v_dict.
  apply fir_cons_nonint. apply not_int_v_str_9.
  apply fir_nil.
Qed.