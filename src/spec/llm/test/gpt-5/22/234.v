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
Parameters n3 n4 n5 n11 : int.
Axiom H3 : IsInt v3 n3.
Axiom H4 : IsInt v4 n4.
Axiom H5 : IsInt v5 n5.
Axiom H11 : IsInt v11 n11.
Axiom N1 : forall n, ~ IsInt v1 n.
Axiom N2 : forall n, ~ IsInt v2 n.
Axiom N6 : forall n, ~ IsInt v6 n.
Axiom N7 : forall n, ~ IsInt v7 n.
Axiom N8 : forall n, ~ IsInt v8 n.
Axiom N9 : forall n, ~ IsInt v9 n.
Axiom N10 : forall n, ~ IsInt v10 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] [n3; n4; n5; n11].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply N1|].
  eapply fir_cons_nonint; [apply N2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply N6|].
  eapply fir_cons_nonint; [apply N7|].
  eapply fir_cons_nonint; [apply N8|].
  eapply fir_cons_nonint; [apply N9|].
  eapply fir_cons_nonint; [apply N10|].
  eapply fir_cons_int; [apply H11|].
  constructor.
Qed.