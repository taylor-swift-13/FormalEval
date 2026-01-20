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

Parameters
  a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 : Any.
Parameters n5 n_minus7 n0 n6 : int.

Axiom H5 : IsInt a5 n5.
Axiom H7 : IsInt a7 n_minus7.
Axiom H8 : IsInt a8 n0.
Axiom H9 : IsInt a9 n6.

Axiom NI1 : forall n, ~ IsInt a1 n.
Axiom NI2 : forall n, ~ IsInt a2 n.
Axiom NI3 : forall n, ~ IsInt a3 n.
Axiom NI4 : forall n, ~ IsInt a4 n.
Axiom NI6 : forall n, ~ IsInt a6 n.
Axiom NI10 : forall n, ~ IsInt a10 n.
Axiom NI11 : forall n, ~ IsInt a11 n.
Axiom NI12 : forall n, ~ IsInt a12 n.
Axiom NI13 : forall n, ~ IsInt a13 n.
Axiom NI14 : forall n, ~ IsInt a14 n.
Axiom NI15 : forall n, ~ IsInt a15 n.
Axiom NI16 : forall n, ~ IsInt a16 n.
Axiom NI17 : forall n, ~ IsInt a17 n.
Axiom NI18 : forall n, ~ IsInt a18 n.
Axiom NI19 : forall n, ~ IsInt a19 n.
Axiom NI20 : forall n, ~ IsInt a20 n.
Axiom NI21 : forall n, ~ IsInt a21 n.
Axiom NI22 : forall n, ~ IsInt a22 n.

Example test_case_new:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16; a17; a18; a19; a20; a21; a22]
    [n5; n_minus7; n0; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NI1|].
  eapply fir_cons_nonint; [apply NI2|].
  eapply fir_cons_nonint; [apply NI3|].
  eapply fir_cons_nonint; [apply NI4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply NI6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_int; [apply H8|].
  eapply fir_cons_int; [apply H9|].
  eapply fir_cons_nonint; [apply NI10|].
  eapply fir_cons_nonint; [apply NI11|].
  eapply fir_cons_nonint; [apply NI12|].
  eapply fir_cons_nonint; [apply NI13|].
  eapply fir_cons_nonint; [apply NI14|].
  eapply fir_cons_nonint; [apply NI15|].
  eapply fir_cons_nonint; [apply NI16|].
  eapply fir_cons_nonint; [apply NI17|].
  eapply fir_cons_nonint; [apply NI18|].
  eapply fir_cons_nonint; [apply NI19|].
  eapply fir_cons_nonint; [apply NI20|].
  eapply fir_cons_nonint; [apply NI21|].
  eapply fir_cons_nonint; [apply NI22|].
  apply fir_nil.
Qed.