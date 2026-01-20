Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Any.

Axiom H1 : forall n, ~ IsInt v1 n.
Axiom H2 : IsInt v2 2%Z.
Axiom H3 : IsInt v3 3%Z.
Axiom H4 : forall n, ~ IsInt v4 n.
Axiom H5 : forall n, ~ IsInt v5 n.
Axiom H6 : IsInt v6 5%Z.
Axiom H7 : forall n, ~ IsInt v7 n.
Axiom H8 : forall n, ~ IsInt v8 n.
Axiom H9 : forall n, ~ IsInt v9 n.
Axiom H10 : forall n, ~ IsInt v10 n.
Axiom H11 : forall n, ~ IsInt v11 n.
Axiom H12 : IsInt v12 5%Z.
Axiom H13 : IsInt v13 3%Z.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13]
    [2%Z; 3%Z; 5%Z; 5%Z; 3%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_int; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_nonint; [apply H9|].
  eapply fir_cons_nonint; [apply H10|].
  eapply fir_cons_nonint; [apply H11|].
  eapply fir_cons_int; [apply H12|].
  eapply fir_cons_int; [apply H13|].
  apply fir_nil.
Qed.