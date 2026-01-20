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

Parameter v_false1 v_false2 v_none v_real13 v_dict1 v_int5a v_list5_7_1 v_int0 v_str_a v_str_b v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list3_4 v_list5_7_2 v_list5_7_3 v_int5b : Any.

Axiom NI_v_false1 : forall n, ~ IsInt v_false1 n.
Axiom NI_v_false2 : forall n, ~ IsInt v_false2 n.
Axiom NI_v_none : forall n, ~ IsInt v_none n.
Axiom NI_v_real13 : forall n, ~ IsInt v_real13 n.
Axiom NI_v_dict1 : forall n, ~ IsInt v_dict1 n.
Axiom Is_v_int5a : IsInt v_int5a 5%Z.
Axiom NI_v_list5_7_1 : forall n, ~ IsInt v_list5_7_1 n.
Axiom Is_v_int0 : IsInt v_int0 0%Z.
Axiom NI_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NI_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NI_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NI_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NI_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NI_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NI_v_list3_4 : forall n, ~ IsInt v_list3_4 n.
Axiom NI_v_list5_7_2 : forall n, ~ IsInt v_list5_7_2 n.
Axiom NI_v_list5_7_3 : forall n, ~ IsInt v_list5_7_3 n.
Axiom Is_v_int5b : IsInt v_int5b 5%Z.

Example test_case_new:
  filter_integers_spec
    [v_false1; v_false2; v_none; v_real13; v_dict1; v_int5a; v_list5_7_1; v_int0; v_str_a; v_str_b; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list3_4; v_list5_7_2; v_list5_7_3; v_int5b]
    [5%Z; 0%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NI_v_false1|].
  eapply fir_cons_nonint; [apply NI_v_false2|].
  eapply fir_cons_nonint; [apply NI_v_none|].
  eapply fir_cons_nonint; [apply NI_v_real13|].
  eapply fir_cons_nonint; [apply NI_v_dict1|].
  eapply fir_cons_int with (n:=5%Z); [apply Is_v_int5a|].
  eapply fir_cons_nonint; [apply NI_v_list5_7_1|].
  eapply fir_cons_int with (n:=0%Z); [apply Is_v_int0|].
  eapply fir_cons_nonint; [apply NI_v_str_a|].
  eapply fir_cons_nonint; [apply NI_v_str_b|].
  eapply fir_cons_nonint; [apply NI_v_empty_list1|].
  eapply fir_cons_nonint; [apply NI_v_empty_list2|].
  eapply fir_cons_nonint; [apply NI_v_empty_dict|].
  eapply fir_cons_nonint; [apply NI_v_dict_ab|].
  eapply fir_cons_nonint; [apply NI_v_list3_4|].
  eapply fir_cons_nonint; [apply NI_v_list5_7_2|].
  eapply fir_cons_nonint; [apply NI_v_list5_7_3|].
  eapply fir_cons_int with (n:=5%Z); [apply Is_v_int5b|].
  constructor.
Qed.