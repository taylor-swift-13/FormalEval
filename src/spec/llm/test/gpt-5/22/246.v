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

Parameter v_true v_false v_none v_real_1_3 v_int_5 v_int_neg7 v_int_1 v_str_a v_str_b v_list_empty1 v_list_empty2 v_obj_empty v_dict_ab12 v_list_ints_3_4 v_list_mixed_5_6_str7 v_false_end : Any.
Parameter n5 nneg7 n1 : int.

Axiom H_true_nonint : forall n, ~ IsInt v_true n.
Axiom H_false_nonint : forall n, ~ IsInt v_false n.
Axiom H_none_nonint : forall n, ~ IsInt v_none n.
Axiom H_real_1_3_nonint : forall n, ~ IsInt v_real_1_3 n.
Axiom H_int_5 : IsInt v_int_5 n5.
Axiom H_int_neg7 : IsInt v_int_neg7 nneg7.
Axiom H_int_1 : IsInt v_int_1 n1.
Axiom H_str_a_nonint : forall n, ~ IsInt v_str_a n.
Axiom H_str_b_nonint : forall n, ~ IsInt v_str_b n.
Axiom H_list_empty1_nonint : forall n, ~ IsInt v_list_empty1 n.
Axiom H_list_empty2_nonint : forall n, ~ IsInt v_list_empty2 n.
Axiom H_obj_empty_nonint : forall n, ~ IsInt v_obj_empty n.
Axiom H_dict_ab12_nonint : forall n, ~ IsInt v_dict_ab12 n.
Axiom H_list_ints_3_4_nonint : forall n, ~ IsInt v_list_ints_3_4 n.
Axiom H_list_mixed_5_6_str7_nonint : forall n, ~ IsInt v_list_mixed_5_6_str7 n.
Axiom H_false_end_nonint : forall n, ~ IsInt v_false_end n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_real_1_3; v_int_5; v_int_neg7; v_int_1; v_str_a; v_str_b; v_list_empty1; v_list_empty2; v_obj_empty; v_dict_ab12; v_list_ints_3_4; v_list_mixed_5_6_str7; v_false_end]
    [n5; nneg7; n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_true_nonint |].
  eapply fir_cons_nonint; [apply H_false_nonint |].
  eapply fir_cons_nonint; [apply H_none_nonint |].
  eapply fir_cons_nonint; [apply H_real_1_3_nonint |].
  eapply fir_cons_int; [apply H_int_5 |].
  eapply fir_cons_int; [apply H_int_neg7 |].
  eapply fir_cons_int; [apply H_int_1 |].
  eapply fir_cons_nonint; [apply H_str_a_nonint |].
  eapply fir_cons_nonint; [apply H_str_b_nonint |].
  eapply fir_cons_nonint; [apply H_list_empty1_nonint |].
  eapply fir_cons_nonint; [apply H_list_empty2_nonint |].
  eapply fir_cons_nonint; [apply H_obj_empty_nonint |].
  eapply fir_cons_nonint; [apply H_dict_ab12_nonint |].
  eapply fir_cons_nonint; [apply H_list_ints_3_4_nonint |].
  eapply fir_cons_nonint; [apply H_list_mixed_5_6_str7_nonint |].
  eapply fir_cons_nonint; [apply H_false_end_nonint |].
  constructor.
Qed.