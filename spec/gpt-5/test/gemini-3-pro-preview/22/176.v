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

Parameter v1 v2 v3 v4 v5 v6 : Any.
Axiom v1_not_int : forall n, ~ IsInt v1 n.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_not_int : forall n, ~ IsInt v6 n.

Example test_filter_integers_complex : filter_integers_spec [v1; v2; v3; v4; v5; v6] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply v1_not_int.
  apply fir_cons_nonint. apply v2_not_int.
  apply fir_cons_nonint. apply v3_not_int.
  apply fir_cons_nonint. apply v4_not_int.
  apply fir_cons_nonint. apply v5_not_int.
  apply fir_cons_nonint. apply v6_not_int.
  apply fir_nil.
Qed.