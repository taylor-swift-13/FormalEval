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

Parameter r1_5 : Any.
Parameter r2_7 : Any.
Parameter r3_0 : Any.
Parameter r_neg_4_6 : Any.

Axiom not_int_r1_5 : forall n, ~ IsInt r1_5 n.
Axiom not_int_r2_7 : forall n, ~ IsInt r2_7 n.
Axiom not_int_r3_0 : forall n, ~ IsInt r3_0 n.
Axiom not_int_r_neg_4_6 : forall n, ~ IsInt r_neg_4_6 n.

Example test_filter_integers_floats : filter_integers_spec [r1_5; r2_7; r3_0; r_neg_4_6] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_r1_5.
  apply fir_cons_nonint. apply not_int_r2_7.
  apply fir_cons_nonint. apply not_int_r3_0.
  apply fir_cons_nonint. apply not_int_r_neg_4_6.
  apply fir_nil.
Qed.