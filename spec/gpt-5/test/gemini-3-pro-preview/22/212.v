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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Parameter i2 i3 i9 : int.

Axiom Hv1 : forall n, ~ IsInt v1 n.
Axiom Hv2 : IsInt v2 i2.
Axiom Hv3 : IsInt v3 i3.
Axiom Hv4 : forall n, ~ IsInt v4 n.
Axiom Hv5 : forall n, ~ IsInt v5 n.
Axiom Hv6 : forall n, ~ IsInt v6 n.
Axiom Hv7 : forall n, ~ IsInt v7 n.
Axiom Hv8 : forall n, ~ IsInt v8 n.
Axiom Hv9 : IsInt v9 i9.
Axiom Hv10 : forall n, ~ IsInt v10 n.

Example test_filter_integers_mixed : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [i2; i3; i9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply Hv1.
  apply fir_cons_int with (n := i2). apply Hv2.
  apply fir_cons_int with (n := i3). apply Hv3.
  apply fir_cons_nonint. apply Hv4.
  apply fir_cons_nonint. apply Hv5.
  apply fir_cons_nonint. apply Hv6.
  apply fir_cons_nonint. apply Hv7.
  apply fir_cons_nonint. apply Hv8.
  apply fir_cons_int with (n := i9). apply Hv9.
  apply fir_cons_nonint. apply Hv10.
  apply fir_nil.
Qed.