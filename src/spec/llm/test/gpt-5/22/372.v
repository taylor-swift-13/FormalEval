Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Any.
Axiom H_non_a1 : forall n, ~ IsInt a1 n.
Axiom H_non_a2 : forall n, ~ IsInt a2 n.
Axiom H_non_a3 : forall n, ~ IsInt a3 n.
Axiom H_non_a4 : forall n, ~ IsInt a4 n.
Axiom H_non_a5 : forall n, ~ IsInt a5 n.
Axiom H_non_a6 : forall n, ~ IsInt a6 n.
Axiom H_int_a7 : IsInt a7 9%Z.
Axiom H_non_a8 : forall n, ~ IsInt a8 n.
Axiom H_non_a9 : forall n, ~ IsInt a9 n.
Axiom H_non_a10 : forall n, ~ IsInt a10 n.
Axiom H_non_a11 : forall n, ~ IsInt a11 n.
Axiom H_non_a12 : forall n, ~ IsInt a12 n.

Example test_case_new:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12]
    [9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply H_non_a1|].
  apply fir_cons_nonint; [apply H_non_a2|].
  apply fir_cons_nonint; [apply H_non_a3|].
  apply fir_cons_nonint; [apply H_non_a4|].
  apply fir_cons_nonint; [apply H_non_a5|].
  apply fir_cons_nonint; [apply H_non_a6|].
  apply (fir_cons_int a7 9%Z); [apply H_int_a7|].
  apply fir_cons_nonint; [apply H_non_a8|].
  apply fir_cons_nonint; [apply H_non_a9|].
  apply fir_cons_nonint; [apply H_non_a10|].
  apply fir_cons_nonint; [apply H_non_a11|].
  apply fir_cons_nonint; [apply H_non_a12|].
  constructor.
Qed.