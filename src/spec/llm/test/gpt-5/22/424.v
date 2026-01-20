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

Parameters
  v_false1 v_false2 v_false3 v_none v_real13
  v_list5_7_a v_str_a v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab
  v_list_3_4 v_list5_7_b v_list5_7_c
  v5_a vneg7 v0 v5_b : Any.

Parameters z5 zm7 z0 : int.

Axiom IsInt_v5_a : IsInt v5_a z5.
Axiom IsInt_vneg7 : IsInt vneg7 zm7.
Axiom IsInt_v0 : IsInt v0 z0.
Axiom IsInt_v5_b : IsInt v5_b z5.

Axiom NonInt_v_false1 : forall n, ~ IsInt v_false1 n.
Axiom NonInt_v_false2 : forall n, ~ IsInt v_false2 n.
Axiom NonInt_v_false3 : forall n, ~ IsInt v_false3 n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_real13 : forall n, ~ IsInt v_real13 n.
Axiom NonInt_v_list5_7_a : forall n, ~ IsInt v_list5_7_a n.
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom NonInt_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list_3_4 : forall n, ~ IsInt v_list_3_4 n.
Axiom NonInt_v_list5_7_b : forall n, ~ IsInt v_list5_7_b n.
Axiom NonInt_v_list5_7_c : forall n, ~ IsInt v_list5_7_c n.

Example test_case_new:
  filter_integers_spec
    [v_false1; v_false2; v_false3; v_none; v_real13; v5_a; v_list5_7_a; vneg7; v0; v_str_a; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_3_4; v_list5_7_b; v_list5_7_c; v5_b]
    [z5; zm7; z0; z5].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_false1|].
  eapply fir_cons_nonint; [apply NonInt_v_false2|].
  eapply fir_cons_nonint; [apply NonInt_v_false3|].
  eapply fir_cons_nonint; [apply NonInt_v_none|].
  eapply fir_cons_nonint; [apply NonInt_v_real13|].
  eapply fir_cons_int; [apply IsInt_v5_a|].
  eapply fir_cons_nonint; [apply NonInt_v_list5_7_a|].
  eapply fir_cons_int; [apply IsInt_vneg7|].
  eapply fir_cons_int; [apply IsInt_v0|].
  eapply fir_cons_nonint; [apply NonInt_v_str_a|].
  eapply fir_cons_nonint; [apply NonInt_v_empty_list1|].
  eapply fir_cons_nonint; [apply NonInt_v_empty_list2|].
  eapply fir_cons_nonint; [apply NonInt_v_empty_dict|].
  eapply fir_cons_nonint; [apply NonInt_v_dict_ab|].
  eapply fir_cons_nonint; [apply NonInt_v_list_3_4|].
  eapply fir_cons_nonint; [apply NonInt_v_list5_7_b|].
  eapply fir_cons_nonint; [apply NonInt_v_list5_7_c|].
  eapply fir_cons_int; [apply IsInt_v5_b|].
  constructor.
Qed.