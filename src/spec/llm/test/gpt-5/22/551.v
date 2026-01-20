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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameter n1 n2 n3 n5 n9 : int.
Axiom H1 : IsInt v1 n1.
Axiom H2 : IsInt v2 n2.
Axiom H3 : IsInt v3 n3.
Axiom H4 : forall n, ~ IsInt v4 n.
Axiom H5 : IsInt v5 n5.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : forall n, ~ IsInt v7 n.
Axiom H8 : forall n, ~ IsInt v8 n.
Axiom H9 : IsInt v9 n9.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [n1; n2; n3; n5; n9].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_int; [apply H9|].
  constructor.
Qed.