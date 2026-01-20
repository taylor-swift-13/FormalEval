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

Parameter v1 : Any.
Parameter v2 : Any.
Parameter v3 : Any.
Parameter v4 : Any.
Parameter v5 : Any.
Parameter v6 : Any.
Parameter v7 : Any.
Parameter v8 : Any.
Parameter v9 : Any.
Parameter v10 : Any.
Parameter v11 : Any.
Parameter v12 : Any.
Parameter v13 : Any.
Parameter v14 : Any.

Parameter i2 : int.
Parameter i3 : int.
Parameter i6 : int.

Axiom H1 : IsInt v1 i2.
Axiom H2 : forall n, ~ IsInt v2 n.
Axiom H3 : IsInt v3 i2.
Axiom H4 : IsInt v4 i3.
Axiom H5 : forall n, ~ IsInt v5 n.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : IsInt v7 i3.
Axiom H8 : forall n, ~ IsInt v8 n.
Axiom H9 : IsInt v9 i6.
Axiom H10 : forall n, ~ IsInt v10 n.
Axiom H11 : forall n, ~ IsInt v11 n.
Axiom H12 : forall n, ~ IsInt v12 n.
Axiom H13 : forall n, ~ IsInt v13 n.
Axiom H14 : forall n, ~ IsInt v14 n.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14]
    [i2; i2; i3; i3; i6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply H2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_nonint; [apply H8|].
  eapply fir_cons_int; [apply H9|].
  eapply fir_cons_nonint; [apply H10|].
  eapply fir_cons_nonint; [apply H11|].
  eapply fir_cons_nonint; [apply H12|].
  eapply fir_cons_nonint; [apply H13|].
  eapply fir_cons_nonint; [apply H14|].
  apply fir_nil.
Qed.