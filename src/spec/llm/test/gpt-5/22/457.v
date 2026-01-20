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

Parameter v_false1 : Any.
Parameter v_false2 : Any.
Parameter v_none : Any.
Parameter v_real_1_3 : Any.
Parameter v_5 : Any.
Parameter v_list_5_string : Any.
Parameter v_neg7 : Any.
Parameter v_0 : Any.
Parameter v_str_a : Any.
Parameter v_str_b : Any.
Parameter v_empty_list1 : Any.
Parameter v_empty_list2 : Any.
Parameter v_empty_dict : Any.
Parameter v_dict_ab_aa : Any.
Parameter v_list_3_4 : Any.
Parameter v_list_5_string2 : Any.

Parameter i5 : int.
Parameter ineg7 : int.
Parameter i0 : int.

Parameter NotInt_v_false1 : forall n, ~ IsInt v_false1 n.
Parameter NotInt_v_false2 : forall n, ~ IsInt v_false2 n.
Parameter NotInt_v_none : forall n, ~ IsInt v_none n.
Parameter NotInt_v_real_1_3 : forall n, ~ IsInt v_real_1_3 n.
Parameter IsInt_v_5 : IsInt v_5 i5.
Parameter NotInt_v_list_5_string : forall n, ~ IsInt v_list_5_string n.
Parameter IsInt_v_neg7 : IsInt v_neg7 ineg7.
Parameter IsInt_v_0 : IsInt v_0 i0.
Parameter NotInt_v_str_a : forall n, ~ IsInt v_str_a n.
Parameter NotInt_v_str_b : forall n, ~ IsInt v_str_b n.
Parameter NotInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Parameter NotInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Parameter NotInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Parameter NotInt_v_dict_ab_aa : forall n, ~ IsInt v_dict_ab_aa n.
Parameter NotInt_v_list_3_4 : forall n, ~ IsInt v_list_3_4 n.
Parameter NotInt_v_list_5_string2 : forall n, ~ IsInt v_list_5_string2 n.

Example test_case_mixed:
  filter_integers_spec
    [v_false1; v_false2; v_none; v_real_1_3; v_5; v_list_5_string; v_neg7; v_0; v_str_a; v_str_b; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab_aa; v_list_3_4; v_list_5_string2]
    [i5; ineg7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NotInt_v_false1|].
  eapply fir_cons_nonint; [exact NotInt_v_false2|].
  eapply fir_cons_nonint; [exact NotInt_v_none|].
  eapply fir_cons_nonint; [exact NotInt_v_real_1_3|].
  eapply fir_cons_int; [exact IsInt_v_5|].
  eapply fir_cons_nonint; [exact NotInt_v_list_5_string|].
  eapply fir_cons_int; [exact IsInt_v_neg7|].
  eapply fir_cons_int; [exact IsInt_v_0|].
  eapply fir_cons_nonint; [exact NotInt_v_str_a|].
  eapply fir_cons_nonint; [exact NotInt_v_str_b|].
  eapply fir_cons_nonint; [exact NotInt_v_empty_list1|].
  eapply fir_cons_nonint; [exact NotInt_v_empty_list2|].
  eapply fir_cons_nonint; [exact NotInt_v_empty_dict|].
  eapply fir_cons_nonint; [exact NotInt_v_dict_ab_aa|].
  eapply fir_cons_nonint; [exact NotInt_v_list_3_4|].
  eapply fir_cons_nonint; [exact NotInt_v_list_5_string2|].
  constructor.
Qed.