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

Parameter v_true v_false v_none v_real v5 v_minus7 v0 v_str_a v_str_b v_empty_list v_empty_set v_dict_ab v_list_34 v_list_56_str : Any.
Parameter i5 im7 i0 : int.
Axiom v_true_nonint : forall n, ~ IsInt v_true n.
Axiom v_false_nonint : forall n, ~ IsInt v_false n.
Axiom v_none_nonint : forall n, ~ IsInt v_none n.
Axiom v_real_nonint : forall n, ~ IsInt v_real n.
Axiom v5_is_int : IsInt v5 i5.
Axiom v_minus7_is_int : IsInt v_minus7 im7.
Axiom v0_is_int : IsInt v0 i0.
Axiom v_str_a_nonint : forall n, ~ IsInt v_str_a n.
Axiom v_str_b_nonint : forall n, ~ IsInt v_str_b n.
Axiom v_empty_list_nonint : forall n, ~ IsInt v_empty_list n.
Axiom v_empty_set_nonint : forall n, ~ IsInt v_empty_set n.
Axiom v_dict_ab_nonint : forall n, ~ IsInt v_dict_ab n.
Axiom v_list_34_nonint : forall n, ~ IsInt v_list_34 n.
Axiom v_list_56_str_nonint : forall n, ~ IsInt v_list_56_str n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_real; v5; v_minus7; v0; v_str_a; v_str_b; v_empty_list; v_empty_set; v_dict_ab; v_list_34; v_list_56_str]
    [i5; im7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_true_nonint |].
  eapply fir_cons_nonint; [apply v_false_nonint |].
  eapply fir_cons_nonint; [apply v_none_nonint |].
  eapply fir_cons_nonint; [apply v_real_nonint |].
  eapply fir_cons_int with (n := i5); [apply v5_is_int |].
  eapply fir_cons_int with (n := im7); [apply v_minus7_is_int |].
  eapply fir_cons_int with (n := i0); [apply v0_is_int |].
  eapply fir_cons_nonint; [apply v_str_a_nonint |].
  eapply fir_cons_nonint; [apply v_str_b_nonint |].
  eapply fir_cons_nonint; [apply v_empty_list_nonint |].
  eapply fir_cons_nonint; [apply v_empty_set_nonint |].
  eapply fir_cons_nonint; [apply v_dict_ab_nonint |].
  eapply fir_cons_nonint; [apply v_list_34_nonint |].
  eapply fir_cons_nonint; [apply v_list_56_str_nonint |].
  apply fir_nil.
Qed.