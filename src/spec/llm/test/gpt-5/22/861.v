Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter a_str_9ieight : Any.
Parameter a15 : Any.
Parameter a_list_2_3 : Any.
Parameter a4 : Any.
Parameter a_list_5_6 : Any.
Parameter a_list_7_str8_7_1 : Any.
Parameter a_empty_list : Any.
Parameter a_list_7_str8_7_2 : Any.
Parameter a_empty_dict : Any.
Parameter a_str_9 : Any.

Axiom isint_a15 : IsInt a15 15%Z.
Axiom isint_a4 : IsInt a4 4%Z.
Axiom notint_a_str_9ieight : forall n, ~ IsInt a_str_9ieight n.
Axiom notint_a_list_2_3 : forall n, ~ IsInt a_list_2_3 n.
Axiom notint_a_list_5_6 : forall n, ~ IsInt a_list_5_6 n.
Axiom notint_a_list_7_str8_7_1 : forall n, ~ IsInt a_list_7_str8_7_1 n.
Axiom notint_a_empty_list : forall n, ~ IsInt a_empty_list n.
Axiom notint_a_list_7_str8_7_2 : forall n, ~ IsInt a_list_7_str8_7_2 n.
Axiom notint_a_empty_dict : forall n, ~ IsInt a_empty_dict n.
Axiom notint_a_str_9 : forall n, ~ IsInt a_str_9 n.

Example test_case_mixed: filter_integers_spec
  [a_str_9ieight; a15; a_list_2_3; a4; a_list_5_6; a_list_7_str8_7_1; a_empty_list; a_list_7_str8_7_2; a_empty_dict; a_str_9]
  [15%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact notint_a_str_9ieight|].
  eapply fir_cons_int; [exact isint_a15|].
  eapply fir_cons_nonint; [exact notint_a_list_2_3|].
  eapply fir_cons_int; [exact isint_a4|].
  eapply fir_cons_nonint; [exact notint_a_list_5_6|].
  eapply fir_cons_nonint; [exact notint_a_list_7_str8_7_1|].
  eapply fir_cons_nonint; [exact notint_a_empty_list|].
  eapply fir_cons_nonint; [exact notint_a_list_7_str8_7_2|].
  eapply fir_cons_nonint; [exact notint_a_empty_dict|].
  eapply fir_cons_nonint; [exact notint_a_str_9|].
  apply fir_nil.
Qed.