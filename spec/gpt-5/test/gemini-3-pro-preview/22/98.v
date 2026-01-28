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

Parameter val_true : Any.
Parameter val_none : Any.
Parameter val_0 : Any.
Parameter val_neg10 : Any.
Parameter val_watermelon : Any.
Parameter val_nil : Any.
Parameter val_empty_dict : Any.
Parameter val_pi : Any.
Parameter val_test : Any.

Parameter int_0 : int.
Parameter int_neg10 : int.

Axiom is_int_0 : IsInt val_0 int_0.
Axiom is_int_neg10 : IsInt val_neg10 int_neg10.

Axiom not_int_true : forall n, ~ IsInt val_true n.
Axiom not_int_none : forall n, ~ IsInt val_none n.
Axiom not_int_watermelon : forall n, ~ IsInt val_watermelon n.
Axiom not_int_nil : forall n, ~ IsInt val_nil n.
Axiom not_int_empty_dict : forall n, ~ IsInt val_empty_dict n.
Axiom not_int_pi : forall n, ~ IsInt val_pi n.
Axiom not_int_test : forall n, ~ IsInt val_test n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [val_true; val_none; val_0; val_neg10; val_watermelon; val_nil; val_empty_dict; val_pi; val_test] 
    [int_0; int_neg10].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_true.
  apply fir_cons_nonint. apply not_int_none.
  apply fir_cons_int with (n := int_0). apply is_int_0.
  apply fir_cons_int with (n := int_neg10). apply is_int_neg10.
  apply fir_cons_nonint. apply not_int_watermelon.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_empty_dict.
  apply fir_cons_nonint. apply not_int_pi.
  apply fir_cons_nonint. apply not_int_test.
  apply fir_nil.
Qed.