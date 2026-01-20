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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Any.
Parameters n1 n2 n3 n6 n12 n13 : int.
Hypothesis H1 : IsInt v1 n1.
Hypothesis H2 : IsInt v2 n2.
Hypothesis H3 : IsInt v3 n3.
Hypothesis H4 : forall n, ~ IsInt v4 n.
Hypothesis H5 : forall n, ~ IsInt v5 n.
Hypothesis H6 : IsInt v6 n6.
Hypothesis H7 : forall n, ~ IsInt v7 n.
Hypothesis H8 : forall n, ~ IsInt v8 n.
Hypothesis H9 : forall n, ~ IsInt v9 n.
Hypothesis H10 : forall n, ~ IsInt v10 n.
Hypothesis H11 : forall n, ~ IsInt v11 n.
Hypothesis H12 : IsInt v12 n12.
Hypothesis H13 : IsInt v13 n13.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13]
    [n1; n2; n3; n6; n12; n13].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_int; [exact H3|].
  eapply fir_cons_nonint; [exact H4|].
  eapply fir_cons_nonint; [exact H5|].
  eapply fir_cons_int; [exact H6|].
  eapply fir_cons_nonint; [exact H7|].
  eapply fir_cons_nonint; [exact H8|].
  eapply fir_cons_nonint; [exact H9|].
  eapply fir_cons_nonint; [exact H10|].
  eapply fir_cons_nonint; [exact H11|].
  eapply fir_cons_int; [exact H12|].
  eapply fir_cons_int; [exact H13|].
  constructor.
Qed.