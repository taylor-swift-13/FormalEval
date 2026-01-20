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
Parameters i10 i8 i9 : int.
Axiom H1 : IsInt a1 i10.
Axiom H2_non : forall n, ~ IsInt a2 n.
Axiom H3_non : forall n, ~ IsInt a3 n.
Axiom H4 : IsInt a4 i8.
Axiom H5_non : forall n, ~ IsInt a5 n.
Axiom H6_non : forall n, ~ IsInt a6 n.
Axiom H7 : IsInt a7 i9.
Axiom H8 : IsInt a8 i9.
Axiom H9_non : forall n, ~ IsInt a9 n.
Axiom H10_non : forall n, ~ IsInt a10 n.
Axiom H11 : IsInt a11 i9.
Axiom H12_non : forall n, ~ IsInt a12 n.

Example test_case_empty:
  filter_integers_spec
    [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12]
    [i10; i8; i9; i9; i9].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply H2_non|].
  eapply fir_cons_nonint; [apply H3_non|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_nonint; [apply H5_non|].
  eapply fir_cons_nonint; [apply H6_non|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_int; [apply H8|].
  eapply fir_cons_nonint; [apply H9_non|].
  eapply fir_cons_nonint; [apply H10_non|].
  eapply fir_cons_int; [apply H11|].
  eapply fir_cons_nonint; [apply H12_non|].
  constructor.
Qed.