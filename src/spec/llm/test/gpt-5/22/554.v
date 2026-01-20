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

Parameter v_false : Any.
Parameter v_None : Any.
Parameter v_real_1_3 : Any.
Parameter v_list_5_string7 : Any.
Parameter v_string_a : Any.
Parameter v_empty_list1 : Any.
Parameter v_empty_list2 : Any.
Parameter v_empty_dict : Any.
Parameter v_dict_ab : Any.
Parameter v_list_3_4 : Any.
Parameter v_big_dict : Any.

Parameter v5 : Any.
Parameter v_neg7 : Any.
Parameter v0 : Any.
Parameter v51 : Any.

Parameter i5 : int.
Parameter i_neg7 : int.
Parameter i0 : int.
Parameter i51 : int.

Axiom IsInt_v5 : IsInt v5 i5.
Axiom IsInt_v_neg7 : IsInt v_neg7 i_neg7.
Axiom IsInt_v0 : IsInt v0 i0.
Axiom IsInt_v51 : IsInt v51 i51.

Axiom NotInt_v_false : forall n, ~ IsInt v_false n.
Axiom NotInt_v_None : forall n, ~ IsInt v_None n.
Axiom NotInt_v_real_1_3 : forall n, ~ IsInt v_real_1_3 n.
Axiom NotInt_v_list_5_string7 : forall n, ~ IsInt v_list_5_string7 n.
Axiom NotInt_v_string_a : forall n, ~ IsInt v_string_a n.
Axiom NotInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NotInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NotInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NotInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NotInt_v_list_3_4 : forall n, ~ IsInt v_list_3_4 n.
Axiom NotInt_v_big_dict : forall n, ~ IsInt v_big_dict n.

Notation "5%Z" := i5.
Notation "-7%Z" := i_neg7.
Notation "0%Z" := i0.
Notation "51%Z" := i51.

Example test_case_complex:
  filter_integers_spec
    [v_false; v_false; v_false; v_None; v_real_1_3; v5; v_list_5_string7; v_neg7; v0; v_string_a; v51; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_3_4; v_big_dict; v_list_5_string7; v_list_5_string7; v5; v_neg7]
    [5%Z; -7%Z; 0%Z; 51%Z; 5%Z; -7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact NotInt_v_false.
  eapply fir_cons_nonint. exact NotInt_v_false.
  eapply fir_cons_nonint. exact NotInt_v_false.
  eapply fir_cons_nonint. exact NotInt_v_None.
  eapply fir_cons_nonint. exact NotInt_v_real_1_3.
  eapply fir_cons_int. apply IsInt_v5.
  eapply fir_cons_nonint. exact NotInt_v_list_5_string7.
  eapply fir_cons_int. apply IsInt_v_neg7.
  eapply fir_cons_int. apply IsInt_v0.
  eapply fir_cons_nonint. exact NotInt_v_string_a.
  eapply fir_cons_int. apply IsInt_v51.
  eapply fir_cons_nonint. exact NotInt_v_empty_list1.
  eapply fir_cons_nonint. exact NotInt_v_empty_list2.
  eapply fir_cons_nonint. exact NotInt_v_empty_dict.
  eapply fir_cons_nonint. exact NotInt_v_dict_ab.
  eapply fir_cons_nonint. exact NotInt_v_list_3_4.
  eapply fir_cons_nonint. exact NotInt_v_big_dict.
  eapply fir_cons_nonint. exact NotInt_v_list_5_string7.
  eapply fir_cons_nonint. exact NotInt_v_list_5_string7.
  eapply fir_cons_int. apply IsInt_v5.
  eapply fir_cons_int. apply IsInt_v_neg7.
  constructor.
Qed.