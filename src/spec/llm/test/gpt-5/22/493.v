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

Parameter v_true1 v_false1 v_none v_real_1_3 v_5Z v_minus7Z v_false2 v_1Z v_str_33 v_str_b v_empty_list1 v_empty_list2 v_empty_set v_dict_ab v_list_34 v_list_567 : Any.

Axiom v_true1_nonint : forall n, ~ IsInt v_true1 n.
Axiom v_false1_nonint : forall n, ~ IsInt v_false1 n.
Axiom v_none_nonint : forall n, ~ IsInt v_none n.
Axiom v_real_1_3_nonint : forall n, ~ IsInt v_real_1_3 n.
Axiom v_false2_nonint : forall n, ~ IsInt v_false2 n.
Axiom v_str_33_nonint : forall n, ~ IsInt v_str_33 n.
Axiom v_str_b_nonint : forall n, ~ IsInt v_str_b n.
Axiom v_empty_list1_nonint : forall n, ~ IsInt v_empty_list1 n.
Axiom v_empty_list2_nonint : forall n, ~ IsInt v_empty_list2 n.
Axiom v_empty_set_nonint : forall n, ~ IsInt v_empty_set n.
Axiom v_dict_ab_nonint : forall n, ~ IsInt v_dict_ab n.
Axiom v_list_34_nonint : forall n, ~ IsInt v_list_34 n.
Axiom v_list_567_nonint : forall n, ~ IsInt v_list_567 n.

Axiom v_5Z_isint : IsInt v_5Z 5%Z.
Axiom v_minus7Z_isint : IsInt v_minus7Z (-7)%Z.
Axiom v_1Z_isint : IsInt v_1Z 1%Z.

Example test_case_mixed:
  filter_integers_spec
    [v_true1; v_false1; v_none; v_real_1_3; v_5Z; v_minus7Z; v_false2; v_1Z; v_str_33; v_str_b; v_empty_list1; v_empty_list2; v_empty_set; v_dict_ab; v_list_34; v_list_567]
    [5%Z; (-7)%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_true1_nonint |].
  eapply fir_cons_nonint; [apply v_false1_nonint |].
  eapply fir_cons_nonint; [apply v_none_nonint |].
  eapply fir_cons_nonint; [apply v_real_1_3_nonint |].
  eapply fir_cons_int; [apply v_5Z_isint |].
  eapply fir_cons_int; [apply v_minus7Z_isint |].
  eapply fir_cons_nonint; [apply v_false2_nonint |].
  eapply fir_cons_int; [apply v_1Z_isint |].
  eapply fir_cons_nonint; [apply v_str_33_nonint |].
  eapply fir_cons_nonint; [apply v_str_b_nonint |].
  eapply fir_cons_nonint; [apply v_empty_list1_nonint |].
  eapply fir_cons_nonint; [apply v_empty_list2_nonint |].
  eapply fir_cons_nonint; [apply v_empty_set_nonint |].
  eapply fir_cons_nonint; [apply v_dict_ab_nonint |].
  eapply fir_cons_nonint; [apply v_list_34_nonint |].
  eapply fir_cons_nonint; [apply v_list_567_nonint |].
  constructor.
Qed.