Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter v1 : Any.
Axiom v1_not_int : forall n, ~ IsInt v1 n.

Parameter v2 : Any.
Axiom v2_is_int : IsInt v2 0%Z.

Parameter v3 : Any.
Axiom v3_not_int : forall n, ~ IsInt v3 n.

Parameter v4 : Any.
Axiom v4_not_int : forall n, ~ IsInt v4 n.

Parameter v5 : Any.
Axiom v5_not_int : forall n, ~ IsInt v5 n.

Parameter v6 : Any.
Axiom v6_not_int : forall n, ~ IsInt v6 n.

Parameter v7 : Any.
Axiom v7_not_int : forall n, ~ IsInt v7 n.

Parameter v8 : Any.
Axiom v8_is_int : IsInt v8 1%Z.

Parameter v9 : Any.
Axiom v9_not_int : forall n, ~ IsInt v9 n.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [0%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply v1_not_int.
  apply fir_cons_int with (n := 0%Z). apply v2_is_int.
  apply fir_cons_nonint. apply v3_not_int.
  apply fir_cons_nonint. apply v4_not_int.
  apply fir_cons_nonint. apply v5_not_int.
  apply fir_cons_nonint. apply v6_not_int.
  apply fir_cons_nonint. apply v7_not_int.
  apply fir_cons_int with (n := 1%Z). apply v8_is_int.
  apply fir_cons_nonint. apply v9_not_int.
  apply fir_nil.
Qed.