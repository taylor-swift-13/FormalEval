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

Parameter v_false v_true v_none v_real v_5Z v_neg7Z v_0Z v_str_a v_str_b v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list_34 v_list_56_7 : Any.
Parameter z5 z_neg7 z0 : int.

Axiom IsInt_v_5Z : IsInt v_5Z z5.
Axiom IsInt_v_neg7Z : IsInt v_neg7Z z_neg7.
Axiom IsInt_v_0Z : IsInt v_0Z z0.

Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_real : forall n, ~ IsInt v_real n.
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NonInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NonInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NonInt_v_list_56_7 : forall n, ~ IsInt v_list_56_7 n.

Example test_case:
  filter_integers_spec
    [v_false; v_true; v_none; v_real; v_5Z; v_neg7Z; v_0Z; v_str_a; v_str_b; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_34; v_list_56_7]
    [z5; z_neg7; z0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact NonInt_v_false.
  eapply fir_cons_nonint. exact NonInt_v_true.
  eapply fir_cons_nonint. exact NonInt_v_none.
  eapply fir_cons_nonint. exact NonInt_v_real.
  eapply fir_cons_int. exact IsInt_v_5Z.
  eapply fir_cons_int. exact IsInt_v_neg7Z.
  eapply fir_cons_int. exact IsInt_v_0Z.
  eapply fir_cons_nonint. exact NonInt_v_str_a.
  eapply fir_cons_nonint. exact NonInt_v_str_b.
  eapply fir_cons_nonint. exact NonInt_v_empty_list1.
  eapply fir_cons_nonint. exact NonInt_v_empty_list2.
  eapply fir_cons_nonint. exact NonInt_v_empty_dict.
  eapply fir_cons_nonint. exact NonInt_v_dict_ab.
  eapply fir_cons_nonint. exact NonInt_v_list_34.
  eapply fir_cons_nonint. exact NonInt_v_list_56_7.
  constructor.
Qed.