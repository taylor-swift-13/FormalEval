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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Any.
Axiom a1_nonint : forall n, ~ IsInt a1 n.
Axiom a2_nonint : forall n, ~ IsInt a2 n.
Axiom a3_nonint : forall n, ~ IsInt a3 n.
Axiom a4_nonint : forall n, ~ IsInt a4 n.
Axiom a5_nonint : forall n, ~ IsInt a5 n.
Axiom a6_nonint : forall n, ~ IsInt a6 n.
Axiom a7_isint : IsInt a7 9%Z.
Axiom a8_nonint : forall n, ~ IsInt a8 n.
Axiom a9_nonint : forall n, ~ IsInt a9 n.
Axiom a10_nonint : forall n, ~ IsInt a10 n.
Axiom a11_nonint : forall n, ~ IsInt a11 n.
Axiom a12_nonint : forall n, ~ IsInt a12 n.
Axiom a13_nonint : forall n, ~ IsInt a13 n.

Example test_case_1: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13] [9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply a1_nonint|].
  eapply fir_cons_nonint; [apply a2_nonint|].
  eapply fir_cons_nonint; [apply a3_nonint|].
  eapply fir_cons_nonint; [apply a4_nonint|].
  eapply fir_cons_nonint; [apply a5_nonint|].
  eapply fir_cons_nonint; [apply a6_nonint|].
  eapply fir_cons_int; [apply a7_isint|].
  eapply fir_cons_nonint; [apply a8_nonint|].
  eapply fir_cons_nonint; [apply a9_nonint|].
  eapply fir_cons_nonint; [apply a10_nonint|].
  eapply fir_cons_nonint; [apply a11_nonint|].
  eapply fir_cons_nonint; [apply a12_nonint|].
  eapply fir_cons_nonint; [apply a13_nonint|].
  apply fir_nil.
Qed.