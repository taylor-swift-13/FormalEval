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

Parameter v_true v_false v_None v_real_1_3 v_5Z v_m7Z v_0Z1 v_str_bdef v_empty1 v_empty2 v_obj_empty v_dict_ab v_list_34 v_list_5_6_str77 v_0Z2 : Any.
Parameter n5Z n_m7Z n0Z1 n0Z2 : int.
Axiom isint_v_5Z : IsInt v_5Z n5Z.
Axiom isint_v_m7Z : IsInt v_m7Z n_m7Z.
Axiom isint_v_0Z1 : IsInt v_0Z1 n0Z1.
Axiom isint_v_0Z2 : IsInt v_0Z2 n0Z2.
Axiom nonint_v_true : forall n, ~ IsInt v_true n.
Axiom nonint_v_false : forall n, ~ IsInt v_false n.
Axiom nonint_v_None : forall n, ~ IsInt v_None n.
Axiom nonint_v_real_1_3 : forall n, ~ IsInt v_real_1_3 n.
Axiom nonint_v_str_bdef : forall n, ~ IsInt v_str_bdef n.
Axiom nonint_v_empty1 : forall n, ~ IsInt v_empty1 n.
Axiom nonint_v_empty2 : forall n, ~ IsInt v_empty2 n.
Axiom nonint_v_obj_empty : forall n, ~ IsInt v_obj_empty n.
Axiom nonint_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom nonint_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom nonint_v_list_5_6_str77 : forall n, ~ IsInt v_list_5_6_str77 n.

Example test_case_new:
  filter_integers_spec
    [v_true; v_false; v_None; v_real_1_3; v_5Z; v_m7Z; v_0Z1; v_str_bdef; v_empty1; v_empty2; v_obj_empty; v_dict_ab; v_list_34; v_list_5_6_str77; v_0Z2]
    [n5Z; n_m7Z; n0Z1; n0Z2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_v_true |].
  eapply fir_cons_nonint; [apply nonint_v_false |].
  eapply fir_cons_nonint; [apply nonint_v_None |].
  eapply fir_cons_nonint; [apply nonint_v_real_1_3 |].
  eapply fir_cons_int; [apply isint_v_5Z |].
  eapply fir_cons_int; [apply isint_v_m7Z |].
  eapply fir_cons_int; [apply isint_v_0Z1 |].
  eapply fir_cons_nonint; [apply nonint_v_str_bdef |].
  eapply fir_cons_nonint; [apply nonint_v_empty1 |].
  eapply fir_cons_nonint; [apply nonint_v_empty2 |].
  eapply fir_cons_nonint; [apply nonint_v_obj_empty |].
  eapply fir_cons_nonint; [apply nonint_v_dict_ab |].
  eapply fir_cons_nonint; [apply nonint_v_list_34 |].
  eapply fir_cons_nonint; [apply nonint_v_list_5_6_str77 |].
  eapply fir_cons_int; [apply isint_v_0Z2 |].
  constructor.
Qed.