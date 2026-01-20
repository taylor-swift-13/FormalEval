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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : Any.
Axiom H1 : IsInt a1 10%Z.
Axiom H2 : forall n, ~ IsInt a2 n.
Axiom H3 : forall n, ~ IsInt a3 n.
Axiom H4 : IsInt a4 8%Z.
Axiom H5 : forall n, ~ IsInt a5 n.
Axiom H6 : forall n, ~ IsInt a6 n.
Axiom H7 : forall n, ~ IsInt a7 n.
Axiom H8 : IsInt a8 9%Z.
Axiom H9 : IsInt a9 9%Z.
Axiom H10 : IsInt a10 6%Z.
Axiom H11 : forall n, ~ IsInt a11 n.
Axiom H12 : forall n, ~ IsInt a12 n.
Axiom H13 : IsInt a13 9%Z.
Axiom H14 : forall n, ~ IsInt a14 n.
Axiom H15 : IsInt a15 9%Z.
Axiom H16 : forall n, ~ IsInt a16 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16] [10%Z; 8%Z; 9%Z; 9%Z; 6%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_nonint; [exact H2|].
  eapply fir_cons_nonint; [exact H3|].
  eapply fir_cons_int; [exact H4|].
  eapply fir_cons_nonint; [exact H5|].
  eapply fir_cons_nonint; [exact H6|].
  eapply fir_cons_nonint; [exact H7|].
  eapply fir_cons_int; [exact H8|].
  eapply fir_cons_int; [exact H9|].
  eapply fir_cons_int; [exact H10|].
  eapply fir_cons_nonint; [exact H11|].
  eapply fir_cons_nonint; [exact H12|].
  eapply fir_cons_int; [exact H13|].
  eapply fir_cons_nonint; [exact H14|].
  eapply fir_cons_int; [exact H15|].
  eapply fir_cons_nonint; [exact H16|].
  apply fir_nil.
Qed.