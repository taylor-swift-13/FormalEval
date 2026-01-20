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
  v_true1 v_false1 v_none1 v_real1 v5 v_none2 v_neg7 v0 v_str_a v_str_b
  v_empty_list v_real_list v_empty_obj v_dict v_list34 v_list567 v_none3
  v_list34_2 v_real_list_2 v_false2 v_str_a2 : Any.

Parameters
  H_true1_nonint : forall n:int, ~ IsInt v_true1 n.
Parameters
  H_false1_nonint : forall n:int, ~ IsInt v_false1 n.
Parameters
  H_none1_nonint : forall n:int, ~ IsInt v_none1 n.
Parameters
  H_real1_nonint : forall n:int, ~ IsInt v_real1 n.
Parameters
  H_v5_int : IsInt v5 5%Z.
Parameters
  H_none2_nonint : forall n:int, ~ IsInt v_none2 n.
Parameters
  H_vneg7_int : IsInt v_neg7 (-7)%Z.
Parameters
  H_v0_int : IsInt v0 0%Z.
Parameters
  H_str_a_nonint : forall n:int, ~ IsInt v_str_a n.
Parameters
  H_str_b_nonint : forall n:int, ~ IsInt v_str_b n.
Parameters
  H_empty_list_nonint : forall n:int, ~ IsInt v_empty_list n.
Parameters
  H_real_list_nonint : forall n:int, ~ IsInt v_real_list n.
Parameters
  H_empty_obj_nonint : forall n:int, ~ IsInt v_empty_obj n.
Parameters
  H_dict_nonint : forall n:int, ~ IsInt v_dict n.
Parameters
  H_list34_nonint : forall n:int, ~ IsInt v_list34 n.
Parameters
  H_list567_nonint : forall n:int, ~ IsInt v_list567 n.
Parameters
  H_none3_nonint : forall n:int, ~ IsInt v_none3 n.
Parameters
  H_list34_2_nonint : forall n:int, ~ IsInt v_list34_2 n.
Parameters
  H_real_list_2_nonint : forall n:int, ~ IsInt v_real_list_2 n.
Parameters
  H_false2_nonint : forall n:int, ~ IsInt v_false2 n.
Parameters
  H_str_a2_nonint : forall n:int, ~ IsInt v_str_a2 n.

Example test_case_new:
  filter_integers_spec
    [v_true1; v_false1; v_none1; v_real1; v5; v_none2; v_neg7; v0; v_str_a; v_str_b; v_empty_list; v_real_list; v_empty_obj; v_dict; v_list34; v_list567; v_none3; v_list34_2; v_real_list_2; v_false2; v_str_a2]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact H_true1_nonint.
  eapply fir_cons_nonint. exact H_false1_nonint.
  eapply fir_cons_nonint. exact H_none1_nonint.
  eapply fir_cons_nonint. exact H_real1_nonint.
  eapply fir_cons_int. exact H_v5_int.
  eapply fir_cons_nonint. exact H_none2_nonint.
  eapply fir_cons_int. exact H_vneg7_int.
  eapply fir_cons_int. exact H_v0_int.
  eapply fir_cons_nonint. exact H_str_a_nonint.
  eapply fir_cons_nonint. exact H_str_b_nonint.
  eapply fir_cons_nonint. exact H_empty_list_nonint.
  eapply fir_cons_nonint. exact H_real_list_nonint.
  eapply fir_cons_nonint. exact H_empty_obj_nonint.
  eapply fir_cons_nonint. exact H_dict_nonint.
  eapply fir_cons_nonint. exact H_list34_nonint.
  eapply fir_cons_nonint. exact H_list567_nonint.
  eapply fir_cons_nonint. exact H_none3_nonint.
  eapply fir_cons_nonint. exact H_list34_2_nonint.
  eapply fir_cons_nonint. exact H_real_list_2_nonint.
  eapply fir_cons_nonint. exact H_false2_nonint.
  eapply fir_cons_nonint. exact H_str_a2_nonint.
  constructor.
Qed.