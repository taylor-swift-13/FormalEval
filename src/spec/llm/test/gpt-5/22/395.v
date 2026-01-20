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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Hypothesis H1 : IsInt v1 10%Z.
Hypothesis H2_non : forall n, ~ IsInt v2 n.
Hypothesis H3_non : forall n, ~ IsInt v3 n.
Hypothesis H4_non : forall n, ~ IsInt v4 n.
Hypothesis H5_non : forall n, ~ IsInt v5 n.
Hypothesis H6_non : forall n, ~ IsInt v6 n.
Hypothesis H7_non : forall n, ~ IsInt v7 n.
Hypothesis H8 : IsInt v8 10%Z.
Hypothesis H9_non : forall n, ~ IsInt v9 n.
Hypothesis H10_non : forall n, ~ IsInt v10 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [10%Z; 10%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_nonint; [exact H2_non|].
  eapply fir_cons_nonint; [exact H3_non|].
  eapply fir_cons_nonint; [exact H4_non|].
  eapply fir_cons_nonint; [exact H5_non|].
  eapply fir_cons_nonint; [exact H6_non|].
  eapply fir_cons_nonint; [exact H7_non|].
  eapply fir_cons_int; [exact H8|].
  eapply fir_cons_nonint; [exact H9_non|].
  eapply fir_cons_nonint; [exact H10_non|].
  constructor.
Qed.