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
  forall a1 a2 a3 a4 a5 a6 a7 a8 : Any,
  forall n6 n2 n1 : int,
  IsInt a1 n6 ->
  IsInt a2 n2 ->
  (forall n, ~ IsInt a3 n) ->
  IsInt a4 n1 ->
  (forall n, ~ IsInt a5 n) ->
  (forall n, ~ IsInt a6 n) ->
  (forall n, ~ IsInt a7 n) ->
  (forall n, ~ IsInt a8 n) ->
  filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8] [n6; n2; n1].
Proof.
  unfold filter_integers_spec.
  intros a1 a2 a3 a4 a5 a6 a7 a8 n6 n2 n1 H1 H2 H3 H4 H5 H6 H7 H8.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_nonint; [exact H3|].
  eapply fir_cons_int; [exact H4|].
  eapply fir_cons_nonint; [exact H5|].
  eapply fir_cons_nonint; [exact H6|].
  eapply fir_cons_nonint; [exact H7|].
  eapply fir_cons_nonint; [exact H8|].
  constructor.
Qed.