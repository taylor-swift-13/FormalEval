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

Parameter v_str_2 : Any.
Parameter v_obj_empty : Any.
Parameter v_list_1_2_3 : Any.
Parameter v_list_4_5 : Any.
Parameter v_str_wsYK : Any.
Parameter v_int_0 : Any.

Axiom not_int_v_str_2 : forall n, ~ IsInt v_str_2 n.
Axiom not_int_v_obj_empty : forall n, ~ IsInt v_obj_empty n.
Axiom not_int_v_list_1_2_3 : forall n, ~ IsInt v_list_1_2_3 n.
Axiom not_int_v_list_4_5 : forall n, ~ IsInt v_list_4_5 n.
Axiom not_int_v_str_wsYK : forall n, ~ IsInt v_str_wsYK n.
Axiom is_int_v_int_0 : IsInt v_int_0 0%Z.

Example test_case_mixed:
  filter_integers_spec
    [v_str_2; v_obj_empty; v_list_1_2_3; v_list_4_5; v_str_wsYK; v_int_0]
    [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply not_int_v_str_2|].
  eapply fir_cons_nonint; [apply not_int_v_obj_empty|].
  eapply fir_cons_nonint; [apply not_int_v_list_1_2_3|].
  eapply fir_cons_nonint; [apply not_int_v_list_4_5|].
  eapply fir_cons_nonint; [apply not_int_v_str_wsYK|].
  eapply fir_cons_int; [apply is_int_v_int_0|].
  constructor.
Qed.