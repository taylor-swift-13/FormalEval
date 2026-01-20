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

Parameters v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameters n0 n2 n4 : int.
Axiom H_v0 : IsInt v0 n0.
Axiom H_v1 : IsInt v1 n2.
Axiom H_v2 : forall n, ~ IsInt v2 n.
Axiom H_v3 : IsInt v3 n4.
Axiom H_v4 : forall n, ~ IsInt v4 n.
Axiom H_v5 : forall n, ~ IsInt v5 n.
Axiom H_v6 : forall n, ~ IsInt v6 n.
Axiom H_v7 : forall n, ~ IsInt v7 n.
Axiom H_v8 : forall n, ~ IsInt v8 n.
Axiom H_v9 : forall n, ~ IsInt v9 n.

Example test_case_1: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9] [n0; n2; n4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. exact H_v0.
  eapply fir_cons_int. exact H_v1.
  eapply fir_cons_nonint. exact H_v2.
  eapply fir_cons_int. exact H_v3.
  eapply fir_cons_nonint. exact H_v4.
  eapply fir_cons_nonint. exact H_v5.
  eapply fir_cons_nonint. exact H_v6.
  eapply fir_cons_nonint. exact H_v7.
  eapply fir_cons_nonint. exact H_v8.
  eapply fir_cons_nonint. exact H_v9.
  constructor.
Qed.