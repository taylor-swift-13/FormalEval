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

Parameters v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Parameters n0 n1 n3 n5 n7 : int.
Axiom is_v0 : IsInt v0 n0.
Axiom is_v1 : IsInt v1 n1.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom is_v3 : IsInt v3 n3.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom is_v5 : IsInt v5 n5.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom is_v7 : IsInt v7 n7.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.
Axiom v10_nonint : forall n, ~ IsInt v10 n.

Example test_case_new:
  filter_integers_spec
    [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10]
    [n0; n1; n3; n5; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact is_v0|].
  eapply fir_cons_int; [exact is_v1|].
  eapply fir_cons_nonint; [exact v2_nonint|].
  eapply fir_cons_int; [exact is_v3|].
  eapply fir_cons_nonint; [exact v4_nonint|].
  eapply fir_cons_int; [exact is_v5|].
  eapply fir_cons_nonint; [exact v6_nonint|].
  eapply fir_cons_int; [exact is_v7|].
  eapply fir_cons_nonint; [exact v8_nonint|].
  eapply fir_cons_nonint; [exact v9_nonint|].
  eapply fir_cons_nonint; [exact v10_nonint|].
  constructor.
Qed.