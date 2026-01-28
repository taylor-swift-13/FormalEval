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

Section Test_Case.
  Variable v1 v8 v9 v_nil v_l5 v_l8 : Any.
  Variable i1 i8 i9 : int.

  Hypothesis H_v1 : IsInt v1 i1.
  Hypothesis H_v8 : IsInt v8 i8.
  Hypothesis H_v9 : IsInt v9 i9.

  Hypothesis H_nil : forall n, ~ IsInt v_nil n.
  Hypothesis H_l5 : forall n, ~ IsInt v_l5 n.
  Hypothesis H_l8 : forall n, ~ IsInt v_l8 n.

  Example test_filter_integers : 
    filter_integers_spec 
      [v1; v_nil; v8; v_l5; v_l8; v9; v9; v_nil; v_l8] 
      [i1; i8; i9; i9].
  Proof.
    unfold filter_integers_spec.
    apply fir_cons_int. exact H_v1.
    apply fir_cons_nonint. exact H_nil.
    apply fir_cons_int. exact H_v8.
    apply fir_cons_nonint. exact H_l5.
    apply fir_cons_nonint. exact H_l8.
    apply fir_cons_int. exact H_v9.
    apply fir_cons_int. exact H_v9.
    apply fir_cons_nonint. exact H_nil.
    apply fir_cons_nonint. exact H_l8.
    apply fir_nil.
  Qed.
End Test_Case.