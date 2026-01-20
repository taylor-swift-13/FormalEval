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

Example test_case_mixed:
  forall v1 v2 v3 v4 v5 v6 v7 v8 n1 n2 n3 n4 n5,
    IsInt v1 n1 ->
    IsInt v2 n2 ->
    IsInt v3 n3 ->
    IsInt v4 n4 ->
    (forall n, ~ IsInt v5 n) ->
    IsInt v6 n5 ->
    (forall n, ~ IsInt v7 n) ->
    (forall n, ~ IsInt v8 n) ->
    filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [n1; n2; n3; n4; n5].
Proof.
  intros v1 v2 v3 v4 v5 v6 v7 v8 n1 n2 n3 n4 n5 H1 H2 H3 H4 H5 H6 H7 H8.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1 |].
  eapply fir_cons_int; [exact H2 |].
  eapply fir_cons_int; [exact H3 |].
  eapply fir_cons_int; [exact H4 |].
  eapply fir_cons_nonint; [exact H5 |].
  eapply fir_cons_int; [exact H6 |].
  eapply fir_cons_nonint; [exact H7 |].
  eapply fir_cons_nonint; [exact H8 |].
  constructor.
Qed.