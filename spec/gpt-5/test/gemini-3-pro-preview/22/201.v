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

Section Test.
  Variable v10 : Any.
  Variable v9 : Any.
  Variable v_nil : Any.
  Variable v_complex : Any.
  Variable v_list5 : Any.
  Variable v_list9 : Any.
  
  Variable n10 : int.
  Variable n9 : int.

  Hypothesis H_v10 : IsInt v10 n10.
  Hypothesis H_v9 : IsInt v9 n9.
  
  Hypothesis H_not_nil : forall n, ~ IsInt v_nil n.
  Hypothesis H_not_complex : forall n, ~ IsInt v_complex n.
  Hypothesis H_not_list5 : forall n, ~ IsInt v_list5 n.
  Hypothesis H_not_list9 : forall n, ~ IsInt v_list9 n.

  Let values := [v10; v_nil; v_complex; v_list5; v_list9; v9; v9; v_nil; v_list9; v9; v_list9; v9].
  Let res := [n10; n9; n9; n9; n9].

  Example test_filter_integers : filter_integers_spec values res.
  Proof.
    unfold filter_integers_spec.
    apply fir_cons_int. exact H_v10.
    apply fir_cons_nonint. exact H_not_nil.
    apply fir_cons_nonint. exact H_not_complex.
    apply fir_cons_nonint. exact H_not_list5.
    apply fir_cons_nonint. exact H_not_list9.
    apply fir_cons_int. exact H_v9.
    apply fir_cons_int. exact H_v9.
    apply fir_cons_nonint. exact H_not_nil.
    apply fir_cons_nonint. exact H_not_list9.
    apply fir_cons_int. exact H_v9.
    apply fir_cons_nonint. exact H_not_list9.
    apply fir_cons_int. exact H_v9.
    apply fir_nil.
  Qed.
End Test.