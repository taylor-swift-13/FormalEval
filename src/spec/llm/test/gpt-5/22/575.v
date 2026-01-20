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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : Any.
Parameter n5 n7 n8 : int.

Axiom H1 : forall n, ~ IsInt v1 n.
Axiom H2 : forall n, ~ IsInt v2 n.
Axiom H3 : forall n, ~ IsInt v3 n.
Axiom H4 : forall n, ~ IsInt v4 n.
Axiom H5 : IsInt v5 n5.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : IsInt v7 n7.
Axiom H8 : IsInt v8 n8.
Axiom H9 : forall n, ~ IsInt v9 n.
Axiom H10 : forall n, ~ IsInt v10 n.
Axiom H11 : forall n, ~ IsInt v11 n.
Axiom H12 : forall n, ~ IsInt v12 n.
Axiom H13 : forall n, ~ IsInt v13 n.
Axiom H14 : forall n, ~ IsInt v14 n.
Axiom H15 : forall n, ~ IsInt v15 n.
Axiom H16 : forall n, ~ IsInt v16 n.
Axiom H17 : forall n, ~ IsInt v17 n.
Axiom H18 : forall n, ~ IsInt v18 n.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18]
    [n5; n7; n8].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [exact H1|].
  apply fir_cons_nonint; [exact H2|].
  apply fir_cons_nonint; [exact H3|].
  apply fir_cons_nonint; [exact H4|].
  eapply fir_cons_int; [exact H5|].
  apply fir_cons_nonint; [exact H6|].
  eapply fir_cons_int; [exact H7|].
  eapply fir_cons_int; [exact H8|].
  apply fir_cons_nonint; [exact H9|].
  apply fir_cons_nonint; [exact H10|].
  apply fir_cons_nonint; [exact H11|].
  apply fir_cons_nonint; [exact H12|].
  apply fir_cons_nonint; [exact H13|].
  apply fir_cons_nonint; [exact H14|].
  apply fir_cons_nonint; [exact H15|].
  apply fir_cons_nonint; [exact H16|].
  apply fir_cons_nonint; [exact H17|].
  apply fir_cons_nonint; [exact H18|].
  constructor.
Qed.