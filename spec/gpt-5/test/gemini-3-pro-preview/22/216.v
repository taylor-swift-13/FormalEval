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

Parameter v1 : Any. Axiom is_v1 : IsInt v1 1%Z.
Parameter v2 : Any. Axiom not_v2 : forall n, ~ IsInt v2 n.
Parameter v3 : Any. Axiom is_v3 : IsInt v3 4%Z.
Parameter v4 : Any. Axiom not_v4 : forall n, ~ IsInt v4 n.
Parameter v5 : Any. Axiom not_v5 : forall n, ~ IsInt v5 n.
Parameter v6 : Any. Axiom not_v6 : forall n, ~ IsInt v6 n.
Parameter v7 : Any. Axiom not_v7 : forall n, ~ IsInt v7 n.
Parameter v8 : Any. Axiom not_v8 : forall n, ~ IsInt v8 n.
Parameter v9 : Any. Axiom not_v9 : forall n, ~ IsInt v9 n.
Parameter v10 : Any. Axiom is_v10 : IsInt v10 1%Z.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z). apply is_v1.
  apply fir_cons_nonint. apply not_v2.
  apply fir_cons_int with (n := 4%Z). apply is_v3.
  apply fir_cons_nonint. apply not_v4.
  apply fir_cons_nonint. apply not_v5.
  apply fir_cons_nonint. apply not_v6.
  apply fir_cons_nonint. apply not_v7.
  apply fir_cons_nonint. apply not_v8.
  apply fir_cons_nonint. apply not_v9.
  apply fir_cons_int with (n := 1%Z). apply is_v10.
  apply fir_nil.
Qed.