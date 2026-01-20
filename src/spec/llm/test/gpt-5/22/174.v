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
Parameter n1 n4 : int.
Axiom H1 : IsInt v1 n1.
Axiom H2_non : forall n, ~ IsInt v2 n.
Axiom H3 : IsInt v3 n4.
Axiom H4_non : forall n, ~ IsInt v4 n.
Axiom H5_non : forall n, ~ IsInt v5 n.
Axiom H6_non : forall n, ~ IsInt v6 n.
Axiom H7_non : forall n, ~ IsInt v7 n.
Axiom H8_non : forall n, ~ IsInt v8 n.
Axiom H9_non : forall n, ~ IsInt v9 n.
Axiom H10 : IsInt v10 n1.

Example test_case_new:
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [n1; n4; n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1 |].
  eapply fir_cons_nonint; [apply H2_non |].
  eapply fir_cons_int; [apply H3 |].
  eapply fir_cons_nonint; [apply H4_non |].
  eapply fir_cons_nonint; [apply H5_non |].
  eapply fir_cons_nonint; [apply H6_non |].
  eapply fir_cons_nonint; [apply H7_non |].
  eapply fir_cons_nonint; [apply H8_non |].
  eapply fir_cons_nonint; [apply H9_non |].
  eapply fir_cons_int; [apply H10 |].
  apply fir_nil.
Qed.