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
Parameters n2a n2b n3a n3b n6 : int.
Axiom H1n : forall n, ~ IsInt v1 n.
Axiom H2 : IsInt v2 n2a.
Axiom H3n : forall n, ~ IsInt v3 n.
Axiom H4 : IsInt v4 n2b.
Axiom H5 : IsInt v5 n3a.
Axiom H6n : forall n, ~ IsInt v6 n.
Axiom H7 : IsInt v7 n3b.
Axiom H8n : forall n, ~ IsInt v8 n.
Axiom H9 : IsInt v9 n6.
Axiom H10n : forall n, ~ IsInt v10 n.
Axiom H11n : forall n, ~ IsInt v11 n.
Axiom H12n : forall n, ~ IsInt v12 n.
Axiom H13n : forall n, ~ IsInt v13 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13] [n2a; n2b; n3a; n3b; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H1n|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_nonint; [apply H3n|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply H6n|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_nonint; [apply H8n|].
  eapply fir_cons_int; [apply H9|].
  eapply fir_cons_nonint; [apply H10n|].
  eapply fir_cons_nonint; [apply H11n|].
  eapply fir_cons_nonint; [apply H12n|].
  eapply fir_cons_nonint; [apply H13n|].
  constructor.
Qed.