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

Parameters
  v_false v_none1 v5 vneg6 v0 v_str_a v_str_b v_obj_empty v_obj_b2
  v_list_34 v_list_56_s7 v_dict_floats v_none2 : Any.

Axiom H_v_false_nonint : forall n, ~ IsInt v_false n.
Axiom H_v_none1_nonint : forall n, ~ IsInt v_none1 n.
Axiom H_v5_int : IsInt v5 5%Z.
Axiom H_vneg6_int : IsInt vneg6 (-6)%Z.
Axiom H_v0_int : IsInt v0 0%Z.
Axiom H_v_str_a_nonint : forall n, ~ IsInt v_str_a n.
Axiom H_v_str_b_nonint : forall n, ~ IsInt v_str_b n.
Axiom H_v_obj_empty_nonint : forall n, ~ IsInt v_obj_empty n.
Axiom H_v_obj_b2_nonint : forall n, ~ IsInt v_obj_b2 n.
Axiom H_v_list_34_nonint : forall n, ~ IsInt v_list_34 n.
Axiom H_v_list_56_s7_nonint : forall n, ~ IsInt v_list_56_s7 n.
Axiom H_v_dict_floats_nonint : forall n, ~ IsInt v_dict_floats n.
Axiom H_v_none2_nonint : forall n, ~ IsInt v_none2 n.

Example test_case_new:
  filter_integers_spec
    [v_false; v_none1; v5; vneg6; v0; v_str_a; v_str_b; v_obj_empty; v_obj_b2;
     v_list_34; v_list_56_s7; v_dict_floats; v_none2]
    [5%Z; (-6)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_v_false_nonint|].
  eapply fir_cons_nonint; [apply H_v_none1_nonint|].
  eapply fir_cons_int; [apply H_v5_int|].
  eapply fir_cons_int; [apply H_vneg6_int|].
  eapply fir_cons_int; [apply H_v0_int|].
  eapply fir_cons_nonint; [apply H_v_str_a_nonint|].
  eapply fir_cons_nonint; [apply H_v_str_b_nonint|].
  eapply fir_cons_nonint; [apply H_v_obj_empty_nonint|].
  eapply fir_cons_nonint; [apply H_v_obj_b2_nonint|].
  eapply fir_cons_nonint; [apply H_v_list_34_nonint|].
  eapply fir_cons_nonint; [apply H_v_list_56_s7_nonint|].
  eapply fir_cons_nonint; [apply H_v_dict_floats_nonint|].
  eapply fir_cons_nonint; [apply H_v_none2_nonint|].
  constructor.
Qed.