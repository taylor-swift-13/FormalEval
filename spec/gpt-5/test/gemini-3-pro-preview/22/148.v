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

Parameter v1 : Any.
Parameter v2 : Any.
Parameter v4 : Any.
Parameter v_four : Any.
Parameter v_5_5 : Any.
Parameter v7 : Any.
Parameter v_seven : Any.
Parameter v_8 : Any.
Parameter v_9_0 : Any.

Parameter i1 : int.
Parameter i2 : int.
Parameter i4 : int.
Parameter i7 : int.

Axiom H_v1 : IsInt v1 i1.
Axiom H_v2 : IsInt v2 i2.
Axiom H_v4 : IsInt v4 i4.
Axiom H_v_four : forall n, ~ IsInt v_four n.
Axiom H_v_5_5 : forall n, ~ IsInt v_5_5 n.
Axiom H_v7 : IsInt v7 i7.
Axiom H_v_seven : forall n, ~ IsInt v_seven n.
Axiom H_v_8 : forall n, ~ IsInt v_8 n.
Axiom H_v_9_0 : forall n, ~ IsInt v_9_0 n.

Example test_filter_integers : 
  filter_integers_spec 
    [v1; v2; v4; v_four; v_5_5; v7; v_seven; v_8; v_9_0] 
    [i1; i2; i4; i7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply H_v1.
  apply fir_cons_int. apply H_v2.
  apply fir_cons_int. apply H_v4.
  apply fir_cons_nonint. apply H_v_four.
  apply fir_cons_nonint. apply H_v_5_5.
  apply fir_cons_int. apply H_v7.
  apply fir_cons_nonint. apply H_v_seven.
  apply fir_cons_nonint. apply H_v_8.
  apply fir_cons_nonint. apply H_v_9_0.
  apply fir_nil.
Qed.