Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter v_nil : Any.
Parameter v_l5 : Any.
Parameter v_lbools : Any.
Parameter v_l78 : Any.
Parameter v_9 : Any.

Axiom not_int_nil : forall n, ~ IsInt v_nil n.
Axiom not_int_l5 : forall n, ~ IsInt v_l5 n.
Axiom not_int_lbools : forall n, ~ IsInt v_lbools n.
Axiom not_int_l78 : forall n, ~ IsInt v_l78 n.
Axiom is_int_9 : IsInt v_9 9.

Example test_filter_integers : 
  filter_integers_spec 
    [v_nil; v_nil; v_l5; v_lbools; v_l78; v_9; v_9; v_l5] 
    [9; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_l5.
  apply fir_cons_nonint. apply not_int_lbools.
  apply fir_cons_nonint. apply not_int_l78.
  apply fir_cons_int. apply is_int_9.
  apply fir_cons_int. apply is_int_9.
  apply fir_cons_nonint. apply not_int_l5.
  apply fir_nil.
Qed.