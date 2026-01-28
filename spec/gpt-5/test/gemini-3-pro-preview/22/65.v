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

Parameter val1 : Any.
Parameter val2 : Any.
Parameter val3 : Any.

Axiom not_int_val1 : forall n, ~ IsInt val1 n.
Axiom not_int_val2 : forall n, ~ IsInt val2 n.
Axiom not_int_val3 : forall n, ~ IsInt val3 n.

Example test_filter_integers_mixed : filter_integers_spec [val1; val2; val3; val1] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_val1.
  apply fir_cons_nonint. apply not_int_val2.
  apply fir_cons_nonint. apply not_int_val3.
  apply fir_cons_nonint. apply not_int_val1.
  apply fir_nil.
Qed.