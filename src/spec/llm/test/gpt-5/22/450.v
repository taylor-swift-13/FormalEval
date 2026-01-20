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

Parameter v_list8 : Any.
Parameter v_int1 : Any.
Parameter v_list2_3 : Any.
Parameter v_list4 : Any.
Parameter v_list5_6 : Any.
Parameter v_list8b : Any.

Axiom v_list8_nonint : forall n, ~ IsInt v_list8 n.
Axiom v_list2_3_nonint : forall n, ~ IsInt v_list2_3 n.
Axiom v_list4_nonint : forall n, ~ IsInt v_list4 n.
Axiom v_list5_6_nonint : forall n, ~ IsInt v_list5_6 n.
Axiom v_list8b_nonint : forall n, ~ IsInt v_list8b n.
Axiom v_int1_IsInt : IsInt v_int1 1%Z.

Example test_case_nested_single_int:
  filter_integers_spec [v_list8; v_int1; v_list2_3; v_list4; v_list5_6; v_list8b] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_list8_nonint|].
  eapply fir_cons_int; [apply v_int1_IsInt|].
  eapply fir_cons_nonint; [apply v_list2_3_nonint|].
  eapply fir_cons_nonint; [apply v_list4_nonint|].
  eapply fir_cons_nonint; [apply v_list5_6_nonint|].
  eapply fir_cons_nonint; [apply v_list8b_nonint|].
  constructor.
Qed.