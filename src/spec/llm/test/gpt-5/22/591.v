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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 : Any.
Parameters i3 i7 i9 i10 i12 i21 i22 : int.
Axiom H3 : IsInt a3 i3.
Axiom H7 : IsInt a7 i7.
Axiom H9 : IsInt a9 i9.
Axiom H10 : IsInt a10 i10.
Axiom H12 : IsInt a12 i12.
Axiom H21 : IsInt a21 i21.
Axiom H22 : IsInt a22 i22.
Axiom NI1 : forall n, ~ IsInt a1 n.
Axiom NI2 : forall n, ~ IsInt a2 n.
Axiom NI4 : forall n, ~ IsInt a4 n.
Axiom NI5 : forall n, ~ IsInt a5 n.
Axiom NI6 : forall n, ~ IsInt a6 n.
Axiom NI8 : forall n, ~ IsInt a8 n.
Axiom NI11 : forall n, ~ IsInt a11 n.
Axiom NI13 : forall n, ~ IsInt a13 n.
Axiom NI14 : forall n, ~ IsInt a14 n.
Axiom NI15 : forall n, ~ IsInt a15 n.
Axiom NI16 : forall n, ~ IsInt a16 n.
Axiom NI17 : forall n, ~ IsInt a17 n.
Axiom NI18 : forall n, ~ IsInt a18 n.
Axiom NI19 : forall n, ~ IsInt a19 n.
Axiom NI20 : forall n, ~ IsInt a20 n.

Example test_case_empty:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16; a17; a18; a19; a20; a21; a22]
    [i3; i7; i9; i10; i12; i21; i22].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NI1|].
  eapply fir_cons_nonint; [apply NI2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply NI4|].
  eapply fir_cons_nonint; [apply NI5|].
  eapply fir_cons_nonint; [apply NI6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_nonint; [apply NI8|].
  eapply fir_cons_int; [apply H9|].
  eapply fir_cons_int; [apply H10|].
  eapply fir_cons_nonint; [apply NI11|].
  eapply fir_cons_int; [apply H12|].
  eapply fir_cons_nonint; [apply NI13|].
  eapply fir_cons_nonint; [apply NI14|].
  eapply fir_cons_nonint; [apply NI15|].
  eapply fir_cons_nonint; [apply NI16|].
  eapply fir_cons_nonint; [apply NI17|].
  eapply fir_cons_nonint; [apply NI18|].
  eapply fir_cons_nonint; [apply NI19|].
  eapply fir_cons_nonint; [apply NI20|].
  eapply fir_cons_int; [apply H21|].
  eapply fir_cons_int; [apply H22|].
  constructor.
Qed.