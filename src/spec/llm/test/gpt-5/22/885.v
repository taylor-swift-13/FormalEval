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

Parameter a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Any.
Parameter i0 i1 i2 : int.
Axiom H0 : IsInt a0 i0.
Axiom H1 : forall n, ~ IsInt a1 n.
Axiom H2 : forall n, ~ IsInt a2 n.
Axiom H3 : IsInt a3 i1.
Axiom H4 : forall n, ~ IsInt a4 n.
Axiom H5 : IsInt a5 i2.
Axiom H6 : forall n, ~ IsInt a6 n.
Axiom H7 : forall n, ~ IsInt a7 n.
Axiom H8 : forall n, ~ IsInt a8 n.
Axiom H9 : forall n, ~ IsInt a9 n.

Example test_case_1: filter_integers_spec [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] [i0; i1; i2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H0|].
  eapply fir_cons_nonint; [exact H1|].
  eapply fir_cons_nonint; [exact H2|].
  eapply fir_cons_int; [exact H3|].
  eapply fir_cons_nonint; [exact H4|].
  eapply fir_cons_int; [exact H5|].
  eapply fir_cons_nonint; [exact H6|].
  eapply fir_cons_nonint; [exact H7|].
  eapply fir_cons_nonint; [exact H8|].
  eapply fir_cons_nonint; [exact H9|].
  constructor.
Qed.