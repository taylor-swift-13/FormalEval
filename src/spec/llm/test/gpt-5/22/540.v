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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : Any.
Axiom H1_non : forall n, ~ IsInt a1 n.
Axiom H2_int : IsInt a2 88%Z.
Axiom H3_non : forall n, ~ IsInt a3 n.
Axiom H4_non : forall n, ~ IsInt a4 n.
Axiom H5_non : forall n, ~ IsInt a5 n.
Axiom H6_non : forall n, ~ IsInt a6 n.
Axiom H7_int : IsInt a7 9%Z.
Axiom H8_int : IsInt a8 9%Z.
Axiom H9_non : forall n, ~ IsInt a9 n.
Axiom H10_non : forall n, ~ IsInt a10 n.
Axiom H11_non : forall n, ~ IsInt a11 n.
Axiom H12_non : forall n, ~ IsInt a12 n.
Axiom H13_non : forall n, ~ IsInt a13 n.
Axiom H14_int : IsInt a14 9%Z.

Example test_case_new:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14]
    [88%Z; 9%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact H1_non|].
  eapply fir_cons_int; [exact H2_int|].
  eapply fir_cons_nonint; [exact H3_non|].
  eapply fir_cons_nonint; [exact H4_non|].
  eapply fir_cons_nonint; [exact H5_non|].
  eapply fir_cons_nonint; [exact H6_non|].
  eapply fir_cons_int; [exact H7_int|].
  eapply fir_cons_int; [exact H8_int|].
  eapply fir_cons_nonint; [exact H9_non|].
  eapply fir_cons_nonint; [exact H10_non|].
  eapply fir_cons_nonint; [exact H11_non|].
  eapply fir_cons_nonint; [exact H12_non|].
  eapply fir_cons_nonint; [exact H13_non|].
  eapply fir_cons_int; [exact H14_int|].
  constructor.
Qed.