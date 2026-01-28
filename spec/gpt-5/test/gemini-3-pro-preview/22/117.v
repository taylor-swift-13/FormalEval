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

Parameter v_true : Any.
Parameter v_false : Any.
Parameter v_none : Any.
Parameter v_float : Any.
Parameter v_5 : Any.
Parameter v_n7 : Any.
Parameter v_0 : Any.
Parameter v_a : Any.
Parameter v_b : Any.
Parameter v_nil : Any.
Parameter v_l4 : Any.
Parameter v_empty_dict : Any.
Parameter v_dict : Any.
Parameter v_l567 : Any.

Parameter i_5 : int.
Parameter i_n7 : int.
Parameter i_0 : int.

Axiom H_not_int_true : forall n, ~ IsInt v_true n.
Axiom H_not_int_false : forall n, ~ IsInt v_false n.
Axiom H_not_int_none : forall n, ~ IsInt v_none n.
Axiom H_not_int_float : forall n, ~ IsInt v_float n.
Axiom H_is_int_5 : IsInt v_5 i_5.
Axiom H_is_int_n7 : IsInt v_n7 i_n7.
Axiom H_is_int_0 : IsInt v_0 i_0.
Axiom H_not_int_a : forall n, ~ IsInt v_a n.
Axiom H_not_int_b : forall n, ~ IsInt v_b n.
Axiom H_not_int_nil : forall n, ~ IsInt v_nil n.
Axiom H_not_int_l4 : forall n, ~ IsInt v_l4 n.
Axiom H_not_int_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom H_not_int_dict : forall n, ~ IsInt v_dict n.
Axiom H_not_int_l567 : forall n, ~ IsInt v_l567 n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [v_true; v_false; v_none; v_float; v_5; v_n7; v_0; v_a; v_b; v_nil; v_nil; v_l4; v_empty_dict; v_dict; v_l4; v_l567] 
    [i_5; i_n7; i_0].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply H_not_int_true.
  apply fir_cons_nonint. apply H_not_int_false.
  apply fir_cons_nonint. apply H_not_int_none.
  apply fir_cons_nonint. apply H_not_int_float.
  apply fir_cons_int. apply H_is_int_5.
  apply fir_cons_int. apply H_is_int_n7.
  apply fir_cons_int. apply H_is_int_0.
  apply fir_cons_nonint. apply H_not_int_a.
  apply fir_cons_nonint. apply H_not_int_b.
  apply fir_cons_nonint. apply H_not_int_nil.
  apply fir_cons_nonint. apply H_not_int_nil.
  apply fir_cons_nonint. apply H_not_int_l4.
  apply fir_cons_nonint. apply H_not_int_empty_dict.
  apply fir_cons_nonint. apply H_not_int_dict.
  apply fir_cons_nonint. apply H_not_int_l4.
  apply fir_cons_nonint. apply H_not_int_l567.
  apply fir_nil.
Qed.