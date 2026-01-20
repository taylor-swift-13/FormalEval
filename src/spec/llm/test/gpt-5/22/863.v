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

Parameter v_true v_false v_None v_real_1_3 v_5 v_neg7 v_0 v_str_a v_str_bdef v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list_34 v_list_56_str7 v_5_2 : Any.
Parameter i5 i_neg7 i0 i5_2 : int.
Axiom IsInt_v_5 : IsInt v_5 i5.
Axiom IsInt_v_neg7 : IsInt v_neg7 i_neg7.
Axiom IsInt_v_0 : IsInt v_0 i0.
Axiom IsInt_v_5_2 : IsInt v_5_2 i5_2.
Axiom NotInt_v_true : forall n, ~ IsInt v_true n.
Axiom NotInt_v_false : forall n, ~ IsInt v_false n.
Axiom NotInt_v_None : forall n, ~ IsInt v_None n.
Axiom NotInt_v_real_1_3 : forall n, ~ IsInt v_real_1_3 n.
Axiom NotInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NotInt_v_str_bdef : forall n, ~ IsInt v_str_bdef n.
Axiom NotInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NotInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NotInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NotInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NotInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NotInt_v_list_56_str7 : forall n, ~ IsInt v_list_56_str7 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_None; v_real_1_3; v_5; v_neg7; v_0; v_str_a; v_str_bdef; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_34; v_list_56_str7; v_5_2]
    [i5; i_neg7; i0; i5_2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NotInt_v_true |].
  eapply fir_cons_nonint; [apply NotInt_v_false |].
  eapply fir_cons_nonint; [apply NotInt_v_None |].
  eapply fir_cons_nonint; [apply NotInt_v_real_1_3 |].
  eapply fir_cons_int; [apply IsInt_v_5 |].
  eapply fir_cons_int; [apply IsInt_v_neg7 |].
  eapply fir_cons_int; [apply IsInt_v_0 |].
  eapply fir_cons_nonint; [apply NotInt_v_str_a |].
  eapply fir_cons_nonint; [apply NotInt_v_str_bdef |].
  eapply fir_cons_nonint; [apply NotInt_v_empty_list1 |].
  eapply fir_cons_nonint; [apply NotInt_v_empty_list2 |].
  eapply fir_cons_nonint; [apply NotInt_v_empty_dict |].
  eapply fir_cons_nonint; [apply NotInt_v_dict_ab |].
  eapply fir_cons_nonint; [apply NotInt_v_list_34 |].
  eapply fir_cons_nonint; [apply NotInt_v_list_56_str7 |].
  eapply fir_cons_int; [apply IsInt_v_5_2 |].
  apply fir_nil.
Qed.