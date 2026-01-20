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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.
Parameter n1 : int.
Axiom H_a1_int : IsInt a1 n1.
Axiom H_a2_nonint : forall n, ~ IsInt a2 n.
Axiom H_a3_nonint : forall n, ~ IsInt a3 n.
Axiom H_a4_nonint : forall n, ~ IsInt a4 n.
Axiom H_a5_nonint : forall n, ~ IsInt a5 n.
Axiom H_a6_nonint : forall n, ~ IsInt a6 n.
Axiom H_a7_nonint : forall n, ~ IsInt a7 n.
Axiom H_a8_nonint : forall n, ~ IsInt a8 n.
Axiom H_a9_nonint : forall n, ~ IsInt a9 n.
Axiom H_a10_nonint : forall n, ~ IsInt a10 n.

Example test_case_new:
  filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_a1_int|].
  eapply fir_cons_nonint; [apply H_a2_nonint|].
  eapply fir_cons_nonint; [apply H_a3_nonint|].
  eapply fir_cons_nonint; [apply H_a4_nonint|].
  eapply fir_cons_nonint; [apply H_a5_nonint|].
  eapply fir_cons_nonint; [apply H_a6_nonint|].
  eapply fir_cons_nonint; [apply H_a7_nonint|].
  eapply fir_cons_nonint; [apply H_a8_nonint|].
  eapply fir_cons_nonint; [apply H_a9_nonint|].
  eapply fir_cons_nonint; [apply H_a10_nonint|].
  constructor.
Qed.