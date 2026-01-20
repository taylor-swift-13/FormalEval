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

Parameter v_false1 v_false2 v_none v_real13 v_4 v_list5_7_a v_neg7 v_0 v_str_a v_str_b v_empty_list_a v_empty_list_b v_empty_set v_dict_a_b v_list3_4 v_list5_7_b : Any.
Parameter i4 i_neg7 i0 : int.

Axiom is_int_4 : IsInt v_4 i4.
Axiom is_int_neg7 : IsInt v_neg7 i_neg7.
Axiom is_int_0 : IsInt v_0 i0.

Axiom not_int_false1 : forall n, ~ IsInt v_false1 n.
Axiom not_int_false2 : forall n, ~ IsInt v_false2 n.
Axiom not_int_none : forall n, ~ IsInt v_none n.
Axiom not_int_real13 : forall n, ~ IsInt v_real13 n.
Axiom not_int_list5_7_a : forall n, ~ IsInt v_list5_7_a n.
Axiom not_int_str_a : forall n, ~ IsInt v_str_a n.
Axiom not_int_str_b : forall n, ~ IsInt v_str_b n.
Axiom not_int_empty_list_a : forall n, ~ IsInt v_empty_list_a n.
Axiom not_int_empty_list_b : forall n, ~ IsInt v_empty_list_b n.
Axiom not_int_empty_set : forall n, ~ IsInt v_empty_set n.
Axiom not_int_dict_a_b : forall n, ~ IsInt v_dict_a_b n.
Axiom not_int_list3_4 : forall n, ~ IsInt v_list3_4 n.
Axiom not_int_list5_7_b : forall n, ~ IsInt v_list5_7_b n.

Example test_case_new:
  filter_integers_spec
    [v_false1; v_false2; v_none; v_real13; v_4; v_list5_7_a; v_neg7; v_0; v_str_a; v_str_b; v_empty_list_a; v_empty_list_b; v_empty_set; v_dict_a_b; v_list3_4; v_list5_7_b]
    [i4; i_neg7; i0].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint v_false1); [apply not_int_false1 |].
  apply (fir_cons_nonint v_false2); [apply not_int_false2 |].
  apply (fir_cons_nonint v_none); [apply not_int_none |].
  apply (fir_cons_nonint v_real13); [apply not_int_real13 |].
  apply (fir_cons_int v_4 i4); [apply is_int_4 |].
  apply (fir_cons_nonint v_list5_7_a); [apply not_int_list5_7_a |].
  apply (fir_cons_int v_neg7 i_neg7); [apply is_int_neg7 |].
  apply (fir_cons_int v_0 i0); [apply is_int_0 |].
  apply (fir_cons_nonint v_str_a); [apply not_int_str_a |].
  apply (fir_cons_nonint v_str_b); [apply not_int_str_b |].
  apply (fir_cons_nonint v_empty_list_a); [apply not_int_empty_list_a |].
  apply (fir_cons_nonint v_empty_list_b); [apply not_int_empty_list_b |].
  apply (fir_cons_nonint v_empty_set); [apply not_int_empty_set |].
  apply (fir_cons_nonint v_dict_a_b); [apply not_int_dict_a_b |].
  apply (fir_cons_nonint v_list3_4); [apply not_int_list3_4 |].
  apply (fir_cons_nonint v_list5_7_b); [apply not_int_list5_7_b |].
  constructor.
Qed.