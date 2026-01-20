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
Parameters n1 n2 n3 n4 n5 n6 n7 : int.
Axiom H1 : IsInt v1 n1.
Axiom H2 : IsInt v2 n2.
Axiom H3 : IsInt v3 n3.
Axiom H4 : IsInt v4 n4.
Axiom H5non : forall n, ~ IsInt v5 n.
Axiom H6non : forall n, ~ IsInt v6 n.
Axiom H7 : IsInt v7 n5.
Axiom H8non : forall n, ~ IsInt v8 n.
Axiom H9non : forall n, ~ IsInt v9 n.
Axiom H10 : IsInt v10 n6.
Axiom H11 : IsInt v11 n7.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]
    [n1; n2; n3; n4; n5; n6; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. apply H1.
  eapply fir_cons_int. apply H2.
  eapply fir_cons_int. apply H3.
  eapply fir_cons_int. apply H4.
  eapply fir_cons_nonint. apply H5non.
  eapply fir_cons_nonint. apply H6non.
  eapply fir_cons_int. apply H7.
  eapply fir_cons_nonint. apply H8non.
  eapply fir_cons_nonint. apply H9non.
  eapply fir_cons_int. apply H10.
  eapply fir_cons_int. apply H11.
  constructor.
Qed.