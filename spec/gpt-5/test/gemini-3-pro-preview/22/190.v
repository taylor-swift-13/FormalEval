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

Parameter v_false : Any.
Parameter v_None : Any.
Parameter v_1_3 : Any.
Parameter v_5 : Any.
Parameter v_list_5_7 : Any.
Parameter v_neg7 : Any.
Parameter v_0 : Any.
Parameter v_str_a : Any.
Parameter v_str_b : Any.
Parameter v_list_floats : Any.
Parameter v_2_16 : Any.
Parameter v_empty_list : Any.
Parameter v_empty_dict : Any.
Parameter v_dict_a_b : Any.
Parameter v_neg8 : Any.
Parameter v_list_3_4 : Any.

Parameter i_5 : int.
Parameter i_neg7 : int.
Parameter i_0 : int.
Parameter i_neg8 : int.

Axiom is_int_5 : IsInt v_5 i_5.
Axiom is_int_neg7 : IsInt v_neg7 i_neg7.
Axiom is_int_0 : IsInt v_0 i_0.
Axiom is_int_neg8 : IsInt v_neg8 i_neg8.

Axiom not_int_false : forall n, ~ IsInt v_false n.
Axiom not_int_None : forall n, ~ IsInt v_None n.
Axiom not_int_1_3 : forall n, ~ IsInt v_1_3 n.
Axiom not_int_list_5_7 : forall n, ~ IsInt v_list_5_7 n.
Axiom not_int_str_a : forall n, ~ IsInt v_str_a n.
Axiom not_int_str_b : forall n, ~ IsInt v_str_b n.
Axiom not_int_list_floats : forall n, ~ IsInt v_list_floats n.
Axiom not_int_2_16 : forall n, ~ IsInt v_2_16 n.
Axiom not_int_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom not_int_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom not_int_dict_a_b : forall n, ~ IsInt v_dict_a_b n.
Axiom not_int_list_3_4 : forall n, ~ IsInt v_list_3_4 n.

Example test_filter_integers_complex : filter_integers_spec 
  [v_false; v_false; v_None; v_1_3; v_5; v_list_5_7; v_neg7; v_0; v_str_a; v_str_b; v_list_floats; v_2_16; v_empty_list; v_empty_dict; v_dict_a_b; v_neg8; v_list_3_4; v_list_5_7; v_5] 
  [i_5; i_neg7; i_0; i_neg8; i_5].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply not_int_false |].
  apply fir_cons_nonint; [apply not_int_false |].
  apply fir_cons_nonint; [apply not_int_None |].
  apply fir_cons_nonint; [apply not_int_1_3 |].
  apply fir_cons_int with (n := i_5); [apply is_int_5 |].
  apply fir_cons_nonint; [apply not_int_list_5_7 |].
  apply fir_cons_int with (n := i_neg7); [apply is_int_neg7 |].
  apply fir_cons_int with (n := i_0); [apply is_int_0 |].
  apply fir_cons_nonint; [apply not_int_str_a |].
  apply fir_cons_nonint; [apply not_int_str_b |].
  apply fir_cons_nonint; [apply not_int_list_floats |].
  apply fir_cons_nonint; [apply not_int_2_16 |].
  apply fir_cons_nonint; [apply not_int_empty_list |].
  apply fir_cons_nonint; [apply not_int_empty_dict |].
  apply fir_cons_nonint; [apply not_int_dict_a_b |].
  apply fir_cons_int with (n := i_neg8); [apply is_int_neg8 |].
  apply fir_cons_nonint; [apply not_int_list_3_4 |].
  apply fir_cons_nonint; [apply not_int_list_5_7 |].
  apply fir_cons_int with (n := i_5); [apply is_int_5 |].
  apply fir_nil.
Qed.