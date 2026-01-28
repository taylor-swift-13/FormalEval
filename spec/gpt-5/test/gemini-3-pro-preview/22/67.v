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

Parameter val_apple : Any.
Parameter val_float : Any.
Parameter val_none : Any.
Parameter val_false : Any.
Parameter val_watermelon : Any.
Parameter val_42 : Any.
Parameter int_42 : int.

Axiom not_int_apple : forall n, ~ IsInt val_apple n.
Axiom not_int_float : forall n, ~ IsInt val_float n.
Axiom not_int_none : forall n, ~ IsInt val_none n.
Axiom not_int_false : forall n, ~ IsInt val_false n.
Axiom not_int_watermelon : forall n, ~ IsInt val_watermelon n.
Axiom is_int_42 : IsInt val_42 int_42.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [val_apple; val_float; val_none; val_false; val_watermelon; val_42; val_float; val_watermelon] 
    [int_42].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_apple.
  apply fir_cons_nonint. apply not_int_float.
  apply fir_cons_nonint. apply not_int_none.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_watermelon.
  apply fir_cons_int with (n := int_42). apply is_int_42.
  apply fir_cons_nonint. apply not_int_float.
  apply fir_cons_nonint. apply not_int_watermelon.
  apply fir_nil.
Qed.