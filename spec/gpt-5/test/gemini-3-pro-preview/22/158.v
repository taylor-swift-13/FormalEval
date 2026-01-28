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

Parameter v_empty : Any.
Parameter v_list_5 : Any.
Parameter v_list_bools : Any.
Parameter v_list_7_8 : Any.
Parameter v_9 : Any.

Axiom not_int_empty : forall n, ~ IsInt v_empty n.
Axiom not_int_list_5 : forall n, ~ IsInt v_list_5 n.
Axiom not_int_list_bools : forall n, ~ IsInt v_list_bools n.
Axiom not_int_list_7_8 : forall n, ~ IsInt v_list_7_8 n.
Axiom is_int_9 : IsInt v_9 9%Z.

Example test_filter_integers : filter_integers_spec 
  [v_empty; v_empty; v_list_5; v_list_bools; v_list_7_8; v_9; v_9; v_list_5; v_list_bools] 
  [9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_empty.
  apply fir_cons_nonint. apply not_int_empty.
  apply fir_cons_nonint. apply not_int_list_5.
  apply fir_cons_nonint. apply not_int_list_bools.
  apply fir_cons_nonint. apply not_int_list_7_8.
  apply fir_cons_int with (n := 9%Z). apply is_int_9.
  apply fir_cons_int with (n := 9%Z). apply is_int_9.
  apply fir_cons_nonint. apply not_int_list_5.
  apply fir_cons_nonint. apply not_int_list_bools.
  apply fir_nil.
Qed.