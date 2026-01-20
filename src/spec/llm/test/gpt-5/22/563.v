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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : Any.
Parameter i5 i7 i8 i16 i19 : int.
Axiom Hi5 : IsInt a5 i5.
Axiom Hi7 : IsInt a7 i7.
Axiom Hi8 : IsInt a8 i8.
Axiom Hi16 : IsInt a16 i16.
Axiom Hi19 : IsInt a19 i19.
Axiom Hni1 : forall n, ~ IsInt a1 n.
Axiom Hni2 : forall n, ~ IsInt a2 n.
Axiom Hni3 : forall n, ~ IsInt a3 n.
Axiom Hni4 : forall n, ~ IsInt a4 n.
Axiom Hni6 : forall n, ~ IsInt a6 n.
Axiom Hni9 : forall n, ~ IsInt a9 n.
Axiom Hni10 : forall n, ~ IsInt a10 n.
Axiom Hni11 : forall n, ~ IsInt a11 n.
Axiom Hni12 : forall n, ~ IsInt a12 n.
Axiom Hni13 : forall n, ~ IsInt a13 n.
Axiom Hni14 : forall n, ~ IsInt a14 n.
Axiom Hni15 : forall n, ~ IsInt a15 n.
Axiom Hni17 : forall n, ~ IsInt a17 n.
Axiom Hni18 : forall n, ~ IsInt a18 n.

Example test_case_1:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16; a17; a18; a19]
    [i5; i7; i8; i16; i19].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hni1 |].
  eapply fir_cons_nonint; [apply Hni2 |].
  eapply fir_cons_nonint; [apply Hni3 |].
  eapply fir_cons_nonint; [apply Hni4 |].
  eapply fir_cons_int; [apply Hi5 |].
  eapply fir_cons_nonint; [apply Hni6 |].
  eapply fir_cons_int; [apply Hi7 |].
  eapply fir_cons_int; [apply Hi8 |].
  eapply fir_cons_nonint; [apply Hni9 |].
  eapply fir_cons_nonint; [apply Hni10 |].
  eapply fir_cons_nonint; [apply Hni11 |].
  eapply fir_cons_nonint; [apply Hni12 |].
  eapply fir_cons_nonint; [apply Hni13 |].
  eapply fir_cons_nonint; [apply Hni14 |].
  eapply fir_cons_nonint; [apply Hni15 |].
  eapply fir_cons_int; [apply Hi16 |].
  eapply fir_cons_nonint; [apply Hni17 |].
  eapply fir_cons_nonint; [apply Hni18 |].
  eapply fir_cons_int; [apply Hi19 |].
  constructor.
Qed.