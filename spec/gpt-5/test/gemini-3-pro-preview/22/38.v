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

Parameter v_2_7 : Any.
Parameter v_1_5 : Any.
Axiom not_int_2_7 : forall n, ~ IsInt v_2_7 n.
Axiom not_int_1_5 : forall n, ~ IsInt v_1_5 n.

Example test_filter_integers_floats : filter_integers_spec [v_2_7; v_1_5; v_1_5] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply not_int_2_7.
  - apply fir_cons_nonint.
    + apply not_int_1_5.
    + apply fir_cons_nonint.
      * apply not_int_1_5.
      * apply fir_nil.
Qed.