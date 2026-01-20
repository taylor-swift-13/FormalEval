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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Any.
Parameters n1 n3 n6 n7 : int.
Axiom H1 : IsInt v1 n1.
Axiom H2 : forall n, ~ IsInt v2 n.
Axiom H3 : IsInt v3 n3.
Axiom H4 : forall n, ~ IsInt v4 n.
Axiom H5 : forall n, ~ IsInt v5 n.
Axiom H6 : IsInt v6 n6.
Axiom H7 : IsInt v7 n7.
Axiom H8 : forall n, ~ IsInt v8 n.
Axiom H9 : forall n, ~ IsInt v9 n.
Axiom H10 : forall n, ~ IsInt v10 n.
Axiom H11 : forall n, ~ IsInt v11 n.

Example test_case_new :
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]
    [n1; n3; n6; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. exact H1.
  eapply fir_cons_nonint. exact H2.
  eapply fir_cons_int. exact H3.
  eapply fir_cons_nonint. exact H4.
  eapply fir_cons_nonint. exact H5.
  eapply fir_cons_int. exact H6.
  eapply fir_cons_int. exact H7.
  eapply fir_cons_nonint. exact H8.
  eapply fir_cons_nonint. exact H9.
  eapply fir_cons_nonint. exact H10.
  eapply fir_cons_nonint. exact H11.
  constructor.
Qed.