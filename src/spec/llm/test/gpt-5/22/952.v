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

Example test_case_mixed:
  forall (v_true v_false v_none1 v_real v_n7 v_none2 v_zero v_str_a v_str_bdef v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list_34 v_list_56_7 v_five : Any)
         (n7 n0 n5 : int),
    (forall n, ~ IsInt v_true n) ->
    (forall n, ~ IsInt v_false n) ->
    (forall n, ~ IsInt v_none1 n) ->
    (forall n, ~ IsInt v_real n) ->
    IsInt v_n7 n7 ->
    (forall n, ~ IsInt v_none2 n) ->
    IsInt v_zero n0 ->
    (forall n, ~ IsInt v_str_a n) ->
    (forall n, ~ IsInt v_str_bdef n) ->
    (forall n, ~ IsInt v_empty_list1 n) ->
    (forall n, ~ IsInt v_empty_list2 n) ->
    (forall n, ~ IsInt v_empty_dict n) ->
    (forall n, ~ IsInt v_dict_ab n) ->
    (forall n, ~ IsInt v_list_34 n) ->
    (forall n, ~ IsInt v_list_56_7 n) ->
    IsInt v_five n5 ->
    filter_integers_spec
      [v_true; v_false; v_none1; v_real; v_n7; v_none2; v_zero; v_str_a; v_str_bdef; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_34; v_list_56_7; v_five]
      [n7; n0; n5].
Proof.
  intros v_true v_false v_none1 v_real v_n7 v_none2 v_zero v_str_a v_str_bdef v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list_34 v_list_56_7 v_five n7 n0 n5
         Htrue Hfalse Hnone1 Hreal Hn7 Hnone2 Hzero Hstra Hstrbdef Hemptylist1 Hemptylist2 Hemptydict Hdictab Hlist34 Hlist5677 Hfive.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact Htrue|].
  eapply fir_cons_nonint; [exact Hfalse|].
  eapply fir_cons_nonint; [exact Hnone1|].
  eapply fir_cons_nonint; [exact Hreal|].
  eapply fir_cons_int; [exact Hn7|].
  eapply fir_cons_nonint; [exact Hnone2|].
  eapply fir_cons_int; [exact Hzero|].
  eapply fir_cons_nonint; [exact Hstra|].
  eapply fir_cons_nonint; [exact Hstrbdef|].
  eapply fir_cons_nonint; [exact Hemptylist1|].
  eapply fir_cons_nonint; [exact Hemptylist2|].
  eapply fir_cons_nonint; [exact Hemptydict|].
  eapply fir_cons_nonint; [exact Hdictab|].
  eapply fir_cons_nonint; [exact Hlist34|].
  eapply fir_cons_nonint; [exact Hlist5677|].
  eapply fir_cons_int; [exact Hfive|].
  constructor.
Qed.