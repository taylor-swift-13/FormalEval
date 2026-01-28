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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.

Axiom not_int_v1 : forall n, ~ IsInt v1 n.
Axiom is_int_v2 : IsInt v2 2%Z.
Axiom is_int_v3 : IsInt v3 0%Z.
Axiom not_int_v4 : forall n, ~ IsInt v4 n.
Axiom not_int_v5 : forall n, ~ IsInt v5 n.
Axiom not_int_v6 : forall n, ~ IsInt v6 n.
Axiom not_int_v7 : forall n, ~ IsInt v7 n.
Axiom not_int_v8 : forall n, ~ IsInt v8 n.
Axiom is_int_v9 : IsInt v9 1%Z.
Axiom not_int_v10 : forall n, ~ IsInt v10 n.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [2%Z; 0%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_v1.
  apply fir_cons_int with (n := 2%Z). apply is_int_v2.
  apply fir_cons_int with (n := 0%Z). apply is_int_v3.
  apply fir_cons_nonint. apply not_int_v4.
  apply fir_cons_nonint. apply not_int_v5.
  apply fir_cons_nonint. apply not_int_v6.
  apply fir_cons_nonint. apply not_int_v7.
  apply fir_cons_nonint. apply not_int_v8.
  apply fir_cons_int with (n := 1%Z). apply is_int_v9.
  apply fir_cons_nonint. apply not_int_v10.
  apply fir_nil.
Qed.