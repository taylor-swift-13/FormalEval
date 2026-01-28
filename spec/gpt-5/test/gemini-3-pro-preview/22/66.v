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

Parameter r1 r2 r3 r4 : Any.
Axiom r1_not_int : forall n, ~ IsInt r1 n.
Axiom r2_not_int : forall n, ~ IsInt r2 n.
Axiom r3_not_int : forall n, ~ IsInt r3 n.
Axiom r4_not_int : forall n, ~ IsInt r4 n.

Example test_filter_integers_floats : filter_integers_spec [r1; r2; r3; r4] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply r1_not_int.
  apply fir_cons_nonint. apply r2_not_int.
  apply fir_cons_nonint. apply r3_not_int.
  apply fir_cons_nonint. apply r4_not_int.
  apply fir_nil.
Qed.