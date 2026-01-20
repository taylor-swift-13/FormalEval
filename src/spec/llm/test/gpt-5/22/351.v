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

Section TestCase.
Variables v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Variables n1 n6 n7 n8 : int.
Hypothesis H1 : IsInt v1 n1.
Hypothesis H2 : forall n, ~ IsInt v2 n.
Hypothesis H3 : forall n, ~ IsInt v3 n.
Hypothesis H4 : forall n, ~ IsInt v4 n.
Hypothesis H5 : forall n, ~ IsInt v5 n.
Hypothesis H6 : IsInt v6 n6.
Hypothesis H7 : IsInt v7 n7.
Hypothesis H8 : IsInt v8 n8.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [n1; n6; n7; n8].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_int; [apply H6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_int; [apply H8|].
  constructor.
Qed.
End TestCase.