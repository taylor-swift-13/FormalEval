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

Parameter v_true v_false v_none v_real v_5 v_neg7 v_0 v_bdef v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab12 v_list_34 v_list_big1 v_list_last : Any.
Parameter n5 nneg7 n0 : int.

Axiom IsInt_v_5 : IsInt v_5 n5.
Axiom IsInt_v_neg7 : IsInt v_neg7 nneg7.
Axiom IsInt_v_0 : IsInt v_0 n0.

Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_real : forall n, ~ IsInt v_real n.
Axiom NonInt_v_bdef : forall n, ~ IsInt v_bdef n.
Axiom NonInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NonInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_ab12 : forall n, ~ IsInt v_dict_ab12 n.
Axiom NonInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NonInt_v_list_big1 : forall n, ~ IsInt v_list_big1 n.
Axiom NonInt_v_list_last : forall n, ~ IsInt v_list_last n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_real; v_5; v_neg7; v_0; v_bdef; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab12; v_list_34; v_list_big1; v_list_last]
    [n5; nneg7; n0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_true |].
  eapply fir_cons_nonint; [apply NonInt_v_false |].
  eapply fir_cons_nonint; [apply NonInt_v_none |].
  eapply fir_cons_nonint; [apply NonInt_v_real |].
  eapply fir_cons_int with (n := n5); [apply IsInt_v_5 |].
  eapply fir_cons_int with (n := nneg7); [apply IsInt_v_neg7 |].
  eapply fir_cons_int with (n := n0); [apply IsInt_v_0 |].
  eapply fir_cons_nonint; [apply NonInt_v_bdef |].
  eapply fir_cons_nonint; [apply NonInt_v_empty_list1 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty_list2 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty_dict |].
  eapply fir_cons_nonint; [apply NonInt_v_dict_ab12 |].
  eapply fir_cons_nonint; [apply NonInt_v_list_34 |].
  eapply fir_cons_nonint; [apply NonInt_v_list_big1 |].
  eapply fir_cons_nonint; [apply NonInt_v_list_last |].
  apply fir_nil.
Qed.