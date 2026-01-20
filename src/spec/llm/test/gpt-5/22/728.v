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

Parameters v0 v1 v2 v3 v4 v5 v6 v7 v8 : Any.

Axiom v0_isInt : IsInt v0 0%Z.
Axiom v1_nonint : forall n : int, ~ IsInt v1 n.
Axiom v2_nonint : forall n : int, ~ IsInt v2 n.
Axiom v3_isInt : IsInt v3 4%Z.
Axiom v4_nonint : forall n : int, ~ IsInt v4 n.
Axiom v5_isInt : IsInt v5 61%Z.
Axiom v6_nonint : forall n : int, ~ IsInt v6 n.
Axiom v7_nonint : forall n : int, ~ IsInt v7 n.
Axiom v8_nonint : forall n : int, ~ IsInt v8 n.

Example test_case_1: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8] [0%Z; 4%Z; 61%Z].
Proof.
  unfold filter_integers_spec.
  eapply (fir_cons_int v0 0%Z); [apply v0_isInt|].
  eapply (fir_cons_nonint v1); [apply v1_nonint|].
  eapply (fir_cons_nonint v2); [apply v2_nonint|].
  eapply (fir_cons_int v3 4%Z); [apply v3_isInt|].
  eapply (fir_cons_nonint v4); [apply v4_nonint|].
  eapply (fir_cons_int v5 61%Z); [apply v5_isInt|].
  eapply (fir_cons_nonint v6); [apply v6_nonint|].
  eapply (fir_cons_nonint v7); [apply v7_nonint|].
  eapply (fir_cons_nonint v8); [apply v8_nonint|].
  constructor.
Qed.