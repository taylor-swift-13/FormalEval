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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Parameter n1 : int.
Hypothesis H1 : IsInt v1 n1.
Hypothesis H2 : forall n, ~ IsInt v2 n.
Hypothesis H3 : forall n, ~ IsInt v3 n.
Hypothesis H4 : forall n, ~ IsInt v4 n.
Hypothesis H5 : forall n, ~ IsInt v5 n.
Hypothesis H6 : forall n, ~ IsInt v6 n.
Hypothesis H7 : forall n, ~ IsInt v7 n.
Hypothesis H8 : forall n, ~ IsInt v8 n.
Hypothesis H9 : forall n, ~ IsInt v9 n.
Hypothesis H10 : forall n, ~ IsInt v10 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_nonint; [apply H9|].
  eapply fir_cons_nonint; [apply H10|].
  constructor.
Qed.