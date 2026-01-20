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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Any.
Parameters n1 n2 n5 n11 : int.

Axiom H1 : IsInt a1 n1.
Axiom H2 : IsInt a2 n2.
Axiom H3 : forall n, ~ IsInt a3 n.
Axiom H4 : forall n, ~ IsInt a4 n.
Axiom H5 : IsInt a5 n5.
Axiom H6 : forall n, ~ IsInt a6 n.
Axiom H7 : forall n, ~ IsInt a7 n.
Axiom H8 : forall n, ~ IsInt a8 n.
Axiom H9 : forall n, ~ IsInt a9 n.
Axiom H10 : forall n, ~ IsInt a10 n.
Axiom H11 : IsInt a11 n11.
Axiom H12 : forall n, ~ IsInt a12 n.

Example test_case_new:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12]
    [n1; n2; n5; n11].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_nonint; [apply H9|].
  eapply fir_cons_nonint; [apply H10|].
  eapply fir_cons_int; [apply H11|].
  eapply fir_cons_nonint; [apply H12|].
  constructor.
Qed.