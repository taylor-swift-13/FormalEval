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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : Any.
Parameters n5 n7 n8 n18 : int.

Axiom H1_nonint : forall n, ~ IsInt a1 n.
Axiom H2_nonint : forall n, ~ IsInt a2 n.
Axiom H3_nonint : forall n, ~ IsInt a3 n.
Axiom H4_nonint : forall n, ~ IsInt a4 n.
Axiom H5_int : IsInt a5 n5.
Axiom H6_nonint : forall n, ~ IsInt a6 n.
Axiom H7_int : IsInt a7 n7.
Axiom H8_int : IsInt a8 n8.
Axiom H9_nonint : forall n, ~ IsInt a9 n.
Axiom H10_nonint : forall n, ~ IsInt a10 n.
Axiom H11_nonint : forall n, ~ IsInt a11 n.
Axiom H12_nonint : forall n, ~ IsInt a12 n.
Axiom H13_nonint : forall n, ~ IsInt a13 n.
Axiom H14_nonint : forall n, ~ IsInt a14 n.
Axiom H15_nonint : forall n, ~ IsInt a15 n.
Axiom H16_nonint : forall n, ~ IsInt a16 n.
Axiom H17_nonint : forall n, ~ IsInt a17 n.
Axiom H18_int : IsInt a18 n18.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16; a17; a18] [n5; n7; n8; n18].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact H1_nonint |].
  eapply fir_cons_nonint; [exact H2_nonint |].
  eapply fir_cons_nonint; [exact H3_nonint |].
  eapply fir_cons_nonint; [exact H4_nonint |].
  eapply fir_cons_int; [exact H5_int |].
  eapply fir_cons_nonint; [exact H6_nonint |].
  eapply fir_cons_int; [exact H7_int |].
  eapply fir_cons_int; [exact H8_int |].
  eapply fir_cons_nonint; [exact H9_nonint |].
  eapply fir_cons_nonint; [exact H10_nonint |].
  eapply fir_cons_nonint; [exact H11_nonint |].
  eapply fir_cons_nonint; [exact H12_nonint |].
  eapply fir_cons_nonint; [exact H13_nonint |].
  eapply fir_cons_nonint; [exact H14_nonint |].
  eapply fir_cons_nonint; [exact H15_nonint |].
  eapply fir_cons_nonint; [exact H16_nonint |].
  eapply fir_cons_nonint; [exact H17_nonint |].
  eapply fir_cons_int; [exact H18_int |].
  constructor.
Qed.