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

Parameter v_empty : Any.
Parameter v_list_6 : Any.
Parameter v_list_bools : Any.
Parameter v_list_7_8 : Any.
Parameter v_9 : Any.
Parameter i_9 : int.

Axiom not_int_empty : forall n, ~ IsInt v_empty n.
Axiom not_int_list_6 : forall n, ~ IsInt v_list_6 n.
Axiom not_int_list_bools : forall n, ~ IsInt v_list_bools n.
Axiom not_int_list_7_8 : forall n, ~ IsInt v_list_7_8 n.
Axiom is_int_9 : IsInt v_9 i_9.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v_empty; v_empty; v_list_6; v_list_bools; v_list_7_8; v_9; v_list_6] 
    [i_9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_empty.
  apply fir_cons_nonint. apply not_int_empty.
  apply fir_cons_nonint. apply not_int_list_6.
  apply fir_cons_nonint. apply not_int_list_bools.
  apply fir_cons_nonint. apply not_int_list_7_8.
  apply fir_cons_int with (n := i_9). apply is_int_9.
  apply fir_cons_nonint. apply not_int_list_6.
  apply fir_nil.
Qed.