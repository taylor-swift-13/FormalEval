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

Example test_case_new :
  forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Any,
  forall n1 n4 n7 n8 n11 n12 n13 : int,
  IsInt v1 n1 ->
  (forall n, ~ IsInt v2 n) ->
  (forall n, ~ IsInt v3 n) ->
  IsInt v4 n4 ->
  (forall n, ~ IsInt v5 n) ->
  (forall n, ~ IsInt v6 n) ->
  IsInt v7 n7 ->
  IsInt v8 n8 ->
  (forall n, ~ IsInt v9 n) ->
  (forall n, ~ IsInt v10 n) ->
  IsInt v11 n11 ->
  IsInt v12 n12 ->
  IsInt v13 n13 ->
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13]
    [n1; n4; n7; n8; n11; n12; n13].
Proof.
  intros.
  unfold filter_integers_spec.
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_nonint; [assumption|].
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_int; [assumption|].
  eapply fir_cons_int; [assumption|].
  constructor.
Qed.