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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Any.
Parameter n2 n3 n5a n5b n5c : int.
Axiom H1 : IsInt v1 n2.
Axiom H2 : IsInt v2 n3.
Axiom H3 : forall n, ~ IsInt v3 n.
Axiom H4 : forall n, ~ IsInt v4 n.
Axiom H5 : IsInt v5 n5a.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : forall n, ~ IsInt v7 n.
Axiom H8 : forall n, ~ IsInt v8 n.
Axiom H9 : IsInt v9 n5b.
Axiom H10 : forall n, ~ IsInt v10 n.
Axiom H11 : IsInt v11 n5c.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]
    [n2; n3; n5a; n5b; n5c].
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
  eapply fir_cons_int; [apply H9|].
  eapply fir_cons_nonint; [apply H10|].
  eapply fir_cons_int; [apply H11|].
  apply fir_nil.
Qed.