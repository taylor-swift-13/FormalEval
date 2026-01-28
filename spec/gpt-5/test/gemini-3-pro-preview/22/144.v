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

Parameter v_true : Any.
Parameter v_false : Any.
Parameter v_none : Any.
Parameter v_float_1_3 : Any.
Parameter v_int_5 : Any.
Parameter v_int_neg7 : Any.
Parameter v_int_0 : Any.
Parameter v_str_a : Any.
Parameter v_str_b : Any.
Parameter v_list_empty : Any.
Parameter v_list_float : Any.
Parameter v_dict_empty : Any.
Parameter v_dict_ab : Any.
Parameter v_list_34 : Any.
Parameter v_list_567 : Any.

Parameter i_5 : int.
Parameter i_neg7 : int.
Parameter i_0 : int.

Axiom is_int_5 : IsInt v_int_5 i_5.
Axiom is_int_neg7 : IsInt v_int_neg7 i_neg7.
Axiom is_int_0 : IsInt v_int_0 i_0.

Axiom not_int_true : forall n, ~ IsInt v_true n.
Axiom not_int_false : forall n, ~ IsInt v_false n.
Axiom not_int_none : forall n, ~ IsInt v_none n.
Axiom not_int_float_1_3 : forall n, ~ IsInt v_float_1_3 n.
Axiom not_int_str_a : forall n, ~ IsInt v_str_a n.
Axiom not_int_str_b : forall n, ~ IsInt v_str_b n.
Axiom not_int_list_empty : forall n, ~ IsInt v_list_empty n.
Axiom not_int_list_float : forall n, ~ IsInt v_list_float n.
Axiom not_int_dict_empty : forall n, ~ IsInt v_dict_empty n.
Axiom not_int_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom not_int_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom not_int_list_567 : forall n, ~ IsInt v_list_567 n.

Example test_filter_integers_mixed : filter_integers_spec 
  [v_true; v_false; v_none; v_float_1_3; v_int_5; v_int_neg7; v_int_0; v_str_a; v_str_b; v_list_empty; v_list_float; v_dict_empty; v_dict_ab; v_list_34; v_list_567; v_none; v_list_34] 
  [i_5; i_neg7; i_0].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply not_int_true |].
  apply fir_cons_nonint; [apply not_int_false |].
  apply fir_cons_nonint; [apply not_int_none |].
  apply fir_cons_nonint; [apply not_int_float_1_3 |].
  apply fir_cons_int with (n := i_5); [apply is_int_5 |].
  apply fir_cons_int with (n := i_neg7); [apply is_int_neg7 |].
  apply fir_cons_int with (n := i_0); [apply is_int_0 |].
  apply fir_cons_nonint; [apply not_int_str_a |].
  apply fir_cons_nonint; [apply not_int_str_b |].
  apply fir_cons_nonint; [apply not_int_list_empty |].
  apply fir_cons_nonint; [apply not_int_list_float |].
  apply fir_cons_nonint; [apply not_int_dict_empty |].
  apply fir_cons_nonint; [apply not_int_dict_ab |].
  apply fir_cons_nonint; [apply not_int_list_34 |].
  apply fir_cons_nonint; [apply not_int_list_567 |].
  apply fir_cons_nonint; [apply not_int_none |].
  apply fir_cons_nonint; [apply not_int_list_34 |].
  apply fir_nil.
Qed.