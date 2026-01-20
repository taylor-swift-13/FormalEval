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

Example test_case_single_int:
  forall l1 v2 l3 l4 l5 n8,
    (forall n, ~ IsInt l1 n) ->
    IsInt v2 n8 ->
    (forall n, ~ IsInt l3 n) ->
    (forall n, ~ IsInt l4 n) ->
    (forall n, ~ IsInt l5 n) ->
    filter_integers_spec [l1; v2; l3; l4; l5] [n8].
Proof.
  intros l1 v2 l3 l4 l5 n8 Hn1 H2 Hn3 Hn4 Hn5.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact Hn1|].
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_nonint; [exact Hn3|].
  eapply fir_cons_nonint; [exact Hn4|].
  eapply fir_cons_nonint; [exact Hn5|].
  constructor.
Qed.