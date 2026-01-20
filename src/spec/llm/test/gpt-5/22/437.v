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
Parameter v_none : Any.
Parameter v_real13 : Any.
Parameter v_5 : Any.
Parameter v_neg7 : Any.
Parameter v_1 : Any.
Parameter v_str_a : Any.
Parameter v_str_b : Any.
Parameter v_emptylist1 : Any.
Parameter v_emptylist2 : Any.
Parameter v_emptyrecord : Any.
Parameter v_dict_ab12 : Any.
Parameter v_list_34 : Any.
Parameter v_list_56str7 : Any.

Parameter n5 : int.
Parameter nneg7 : int.
Parameter n1 : int.

Axiom isint_v_5 : IsInt v_5 n5.
Axiom isint_v_neg7 : IsInt v_neg7 nneg7.
Axiom isint_v_1 : IsInt v_1 n1.

Axiom not_int_v_true : forall n, ~ IsInt v_true n.
Axiom not_int_v_none : forall n, ~ IsInt v_none n.
Axiom not_int_v_real13 : forall n, ~ IsInt v_real13 n.
Axiom not_int_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom not_int_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom not_int_v_emptylist1 : forall n, ~ IsInt v_emptylist1 n.
Axiom not_int_v_emptylist2 : forall n, ~ IsInt v_emptylist2 n.
Axiom not_int_v_emptyrecord : forall n, ~ IsInt v_emptyrecord n.
Axiom not_int_v_dict_ab12 : forall n, ~ IsInt v_dict_ab12 n.
Axiom not_int_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom not_int_v_list_56str7 : forall n, ~ IsInt v_list_56str7 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_none; v_real13; v_5; v_neg7; v_1; v_str_a; v_str_b; v_emptylist1; v_emptylist2; v_emptyrecord; v_dict_ab12; v_list_34; v_list_56str7]
    [n5; nneg7; n1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [exact not_int_v_true |].
  apply fir_cons_nonint; [exact not_int_v_none |].
  apply fir_cons_nonint; [exact not_int_v_real13 |].
  apply fir_cons_int; [exact isint_v_5 |].
  apply fir_cons_int; [exact isint_v_neg7 |].
  apply fir_cons_int; [exact isint_v_1 |].
  apply fir_cons_nonint; [exact not_int_v_str_a |].
  apply fir_cons_nonint; [exact not_int_v_str_b |].
  apply fir_cons_nonint; [exact not_int_v_emptylist1 |].
  apply fir_cons_nonint; [exact not_int_v_emptylist2 |].
  apply fir_cons_nonint; [exact not_int_v_emptyrecord |].
  apply fir_cons_nonint; [exact not_int_v_dict_ab12 |].
  apply fir_cons_nonint; [exact not_int_v_list_34 |].
  apply fir_cons_nonint; [exact not_int_v_list_56str7 |].
  constructor.
Qed.