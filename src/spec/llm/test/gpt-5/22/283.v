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

Parameter v_true v_false v_none1 v_real1 v_int5 v_int_minus7 v_int0 v_str_a v_str_b v_empty_list v_real_list1 v_empty_set v_dict v_list_34 v_list_56_7 v_none2 v_list_34b v_real_list2 : Any.
Parameter n5 n_minus7 n0 : int.
Axiom H_true_nonint : forall n, ~ IsInt v_true n.
Axiom H_false_nonint : forall n, ~ IsInt v_false n.
Axiom H_none1_nonint : forall n, ~ IsInt v_none1 n.
Axiom H_real1_nonint : forall n, ~ IsInt v_real1 n.
Axiom H_int5 : IsInt v_int5 n5.
Axiom H_int_minus7 : IsInt v_int_minus7 n_minus7.
Axiom H_int0 : IsInt v_int0 n0.
Axiom H_str_a_nonint : forall n, ~ IsInt v_str_a n.
Axiom H_str_b_nonint : forall n, ~ IsInt v_str_b n.
Axiom H_empty_list_nonint : forall n, ~ IsInt v_empty_list n.
Axiom H_real_list1_nonint : forall n, ~ IsInt v_real_list1 n.
Axiom H_empty_set_nonint : forall n, ~ IsInt v_empty_set n.
Axiom H_dict_nonint : forall n, ~ IsInt v_dict n.
Axiom H_list_34_nonint : forall n, ~ IsInt v_list_34 n.
Axiom H_list_56_7_nonint : forall n, ~ IsInt v_list_56_7 n.
Axiom H_none2_nonint : forall n, ~ IsInt v_none2 n.
Axiom H_list_34b_nonint : forall n, ~ IsInt v_list_34b n.
Axiom H_real_list2_nonint : forall n, ~ IsInt v_real_list2 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none1; v_real1; v_int5; v_int_minus7; v_int0; v_str_a; v_str_b; v_empty_list; v_real_list1; v_empty_set; v_dict; v_list_34; v_list_56_7; v_none2; v_list_34b; v_real_list2]
    [n5; n_minus7; n0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact H_true_nonint|].
  eapply fir_cons_nonint; [exact H_false_nonint|].
  eapply fir_cons_nonint; [exact H_none1_nonint|].
  eapply fir_cons_nonint; [exact H_real1_nonint|].
  eapply fir_cons_int; [exact H_int5|].
  eapply fir_cons_int; [exact H_int_minus7|].
  eapply fir_cons_int; [exact H_int0|].
  eapply fir_cons_nonint; [exact H_str_a_nonint|].
  eapply fir_cons_nonint; [exact H_str_b_nonint|].
  eapply fir_cons_nonint; [exact H_empty_list_nonint|].
  eapply fir_cons_nonint; [exact H_real_list1_nonint|].
  eapply fir_cons_nonint; [exact H_empty_set_nonint|].
  eapply fir_cons_nonint; [exact H_dict_nonint|].
  eapply fir_cons_nonint; [exact H_list_34_nonint|].
  eapply fir_cons_nonint; [exact H_list_56_7_nonint|].
  eapply fir_cons_nonint; [exact H_none2_nonint|].
  eapply fir_cons_nonint; [exact H_list_34b_nonint|].
  eapply fir_cons_nonint; [exact H_real_list2_nonint|].
  constructor.
Qed.