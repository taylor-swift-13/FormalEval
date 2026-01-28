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

Parameter v1 v2 v4 v6 : Any.
Parameter i1 i2 i4 i6 : int.
Parameter v_four v_5_5 v_seven v_8 v_9_0 : Any.

Axiom IsInt_v1 : IsInt v1 i1.
Axiom IsInt_v2 : IsInt v2 i2.
Axiom IsInt_v4 : IsInt v4 i4.
Axiom IsInt_v6 : IsInt v6 i6.

Axiom NotInt_four : forall n, ~ IsInt v_four n.
Axiom NotInt_5_5 : forall n, ~ IsInt v_5_5 n.
Axiom NotInt_seven : forall n, ~ IsInt v_seven n.
Axiom NotInt_8 : forall n, ~ IsInt v_8 n.
Axiom NotInt_9_0 : forall n, ~ IsInt v_9_0 n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v1; v2; v4; v_four; v_5_5; v6; v_seven; v_8; v_9_0] 
    [i1; i2; i4; i6].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply IsInt_v1.
  apply fir_cons_int. apply IsInt_v2.
  apply fir_cons_int. apply IsInt_v4.
  apply fir_cons_nonint. apply NotInt_four.
  apply fir_cons_nonint. apply NotInt_5_5.
  apply fir_cons_int. apply IsInt_v6.
  apply fir_cons_nonint. apply NotInt_seven.
  apply fir_cons_nonint. apply NotInt_8.
  apply fir_cons_nonint. apply NotInt_9_0.
  apply fir_nil.
Qed.