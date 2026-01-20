Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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
Parameter v_none1 : Any.
Parameter v_real13 : Any.
Parameter v_int5 : Any.
Parameter v_int_minus7 : Any.
Parameter v_int0 : Any.
Parameter v_str_a : Any.
Parameter v_str_b : Any.
Parameter v_empty_dict : Any.
Parameter v_dict_ab : Any.
Parameter v_list_3_32_4_1 : Any.
Parameter v_list_3_32_4_2 : Any.
Parameter v_list_5_6_7str : Any.
Parameter v_bigdict : Any.
Parameter v_none2 : Any.

Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_none1 : forall n, ~ IsInt v_none1 n.
Axiom NonInt_v_real13 : forall n, ~ IsInt v_real13 n.
Axiom IsInt_v_int5 : IsInt v_int5 5%Z.
Axiom IsInt_v_int_minus7 : IsInt v_int_minus7 (-7)%Z.
Axiom IsInt_v_int0 : IsInt v_int0 0%Z.
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list_3_32_4_1 : forall n, ~ IsInt v_list_3_32_4_1 n.
Axiom NonInt_v_list_3_32_4_2 : forall n, ~ IsInt v_list_3_32_4_2 n.
Axiom NonInt_v_list_5_6_7str : forall n, ~ IsInt v_list_5_6_7str n.
Axiom NonInt_v_bigdict : forall n, ~ IsInt v_bigdict n.
Axiom NonInt_v_none2 : forall n, ~ IsInt v_none2 n.

Example test_case_new:
  filter_integers_spec
    [v_false; v_none1; v_real13; v_int5; v_int_minus7; v_int0; v_str_a; v_str_b; v_empty_dict; v_dict_ab; v_list_3_32_4_1; v_list_3_32_4_2; v_list_5_6_7str; v_bigdict; v_none2]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NonInt_v_false |].
  eapply fir_cons_nonint; [exact NonInt_v_none1 |].
  eapply fir_cons_nonint; [exact NonInt_v_real13 |].
  eapply fir_cons_int; [exact IsInt_v_int5 |].
  eapply fir_cons_int; [exact IsInt_v_int_minus7 |].
  eapply fir_cons_int; [exact IsInt_v_int0 |].
  eapply fir_cons_nonint; [exact NonInt_v_str_a |].
  eapply fir_cons_nonint; [exact NonInt_v_str_b |].
  eapply fir_cons_nonint; [exact NonInt_v_empty_dict |].
  eapply fir_cons_nonint; [exact NonInt_v_dict_ab |].
  eapply fir_cons_nonint; [exact NonInt_v_list_3_32_4_1 |].
  eapply fir_cons_nonint; [exact NonInt_v_list_3_32_4_2 |].
  eapply fir_cons_nonint; [exact NonInt_v_list_5_6_7str |].
  eapply fir_cons_nonint; [exact NonInt_v_bigdict |].
  eapply fir_cons_nonint; [exact NonInt_v_none2 |].
  apply fir_nil.
Qed.