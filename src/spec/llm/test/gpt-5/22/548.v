Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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
Axiom H_v1_non : forall n, ~ IsInt v1 n.
Axiom H_v2_int : IsInt v2 98%Z.
Axiom H_v3_int : IsInt v3 2%Z.
Axiom H_v4_non : forall n, ~ IsInt v4 n.
Axiom H_v5_non : forall n, ~ IsInt v5 n.
Axiom H_v6_non : forall n, ~ IsInt v6 n.
Axiom H_v7_non : forall n, ~ IsInt v7 n.
Axiom H_v8_non : forall n, ~ IsInt v8 n.
Axiom H_v9_non : forall n, ~ IsInt v9 n.
Axiom H_v10_int : IsInt v10 1%Z.
Axiom H_v11_non : forall n, ~ IsInt v11 n.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11]
    [98%Z; 2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_v1_non|].
  eapply fir_cons_int; [apply H_v2_int|].
  eapply fir_cons_int; [apply H_v3_int|].
  eapply fir_cons_nonint; [apply H_v4_non|].
  eapply fir_cons_nonint; [apply H_v5_non|].
  eapply fir_cons_nonint; [apply H_v6_non|].
  eapply fir_cons_nonint; [apply H_v7_non|].
  eapply fir_cons_nonint; [apply H_v8_non|].
  eapply fir_cons_nonint; [apply H_v9_non|].
  eapply fir_cons_int; [apply H_v10_int|].
  eapply fir_cons_nonint; [apply H_v11_non|].
  constructor.
Qed.