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

Axiom H1 : IsInt v1 1%Z.
Axiom H2nonint : forall n, ~ IsInt v2 n.
Axiom H3 : IsInt v3 4%Z.
Axiom H4nonint : forall n, ~ IsInt v4 n.
Axiom H5nonint : forall n, ~ IsInt v5 n.
Axiom H6nonint : forall n, ~ IsInt v6 n.
Axiom H7nonint : forall n, ~ IsInt v7 n.
Axiom H8nonint : forall n, ~ IsInt v8 n.
Axiom H9nonint : forall n, ~ IsInt v9 n.
Axiom H10 : IsInt v10 1%Z.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply H2nonint|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply H4nonint|].
  eapply fir_cons_nonint; [apply H5nonint|].
  eapply fir_cons_nonint; [apply H6nonint|].
  eapply fir_cons_nonint; [apply H7nonint|].
  eapply fir_cons_nonint; [apply H8nonint|].
  eapply fir_cons_nonint; [apply H9nonint|].
  eapply fir_cons_int; [apply H10|].
  constructor.
Qed.