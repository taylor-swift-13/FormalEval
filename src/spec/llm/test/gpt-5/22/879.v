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

Parameter v_true v_false v_None v_5 v_m7 v_0 v_a v_b v_empty_list v_empty_dict v_dict_a1 v_list_34 v_list_56_7 : Any.
Parameter n5 nm7 n0 : int.
Axiom IsInt_v_5 : IsInt v_5 n5.
Axiom IsInt_v_m7 : IsInt v_m7 nm7.
Axiom IsInt_v_0 : IsInt v_0 n0.
Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_None : forall n, ~ IsInt v_None n.
Axiom NonInt_v_a : forall n, ~ IsInt v_a n.
Axiom NonInt_v_b : forall n, ~ IsInt v_b n.
Axiom NonInt_v_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_a1 : forall n, ~ IsInt v_dict_a1 n.
Axiom NonInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NonInt_v_list_56_7 : forall n, ~ IsInt v_list_56_7 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_None; v_5; v_m7; v_0; v_a; v_b; v_empty_list; v_empty_dict; v_dict_a1; v_list_34; v_list_56_7]
    [n5; nm7; n0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact NonInt_v_true.
  eapply fir_cons_nonint. exact NonInt_v_false.
  eapply fir_cons_nonint. exact NonInt_v_None.
  eapply fir_cons_int. exact IsInt_v_5.
  eapply fir_cons_int. exact IsInt_v_m7.
  eapply fir_cons_int. exact IsInt_v_0.
  eapply fir_cons_nonint. exact NonInt_v_a.
  eapply fir_cons_nonint. exact NonInt_v_b.
  eapply fir_cons_nonint. exact NonInt_v_empty_list.
  eapply fir_cons_nonint. exact NonInt_v_empty_dict.
  eapply fir_cons_nonint. exact NonInt_v_dict_a1.
  eapply fir_cons_nonint. exact NonInt_v_list_34.
  eapply fir_cons_nonint. exact NonInt_v_list_56_7.
  constructor.
Qed.