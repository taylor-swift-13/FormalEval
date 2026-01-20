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

Parameter one two four : int.
Notation "1%Z" := one.
Notation "2%Z" := two.
Notation "4%Z" := four.

Axiom H1 : IsInt v1 1%Z.
Axiom H2 : IsInt v2 2%Z.
Axiom H3_non : forall n, ~ IsInt v3 n.
Axiom H4 : IsInt v4 4%Z.
Axiom H5_non : forall n, ~ IsInt v5 n.
Axiom H6_non : forall n, ~ IsInt v6 n.
Axiom H7_non : forall n, ~ IsInt v7 n.
Axiom H8_non : forall n, ~ IsInt v8 n.
Axiom H9_non : forall n, ~ IsInt v9 n.
Axiom H10_non : forall n, ~ IsInt v10 n.
Axiom H11_non : forall n, ~ IsInt v11 n.

Example test_case_mixed:
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] [1%Z; 2%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_nonint; [apply H3_non|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_nonint; [apply H5_non|].
  eapply fir_cons_nonint; [apply H6_non|].
  eapply fir_cons_nonint; [apply H7_non|].
  eapply fir_cons_nonint; [apply H8_non|].
  eapply fir_cons_nonint; [apply H9_non|].
  eapply fir_cons_nonint; [apply H10_non|].
  eapply fir_cons_nonint; [apply H11_non|].
  constructor.
Qed.