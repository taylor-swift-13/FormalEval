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
  forall v1 v2 v3 v4 v5 n,
    IsInt v1 n ->
    (forall m, ~ IsInt v2 m) ->
    (forall m, ~ IsInt v3 m) ->
    (forall m, ~ IsInt v4 m) ->
    (forall m, ~ IsInt v5 m) ->
    filter_integers_spec [v1; v2; v3; v4; v5] [n].
Proof.
  intros v1 v2 v3 v4 v5 n H1 H2 H3 H4 H5.
  unfold filter_integers_spec.
  apply fir_cons_int; [exact H1|].
  apply fir_cons_nonint; [exact H2|].
  apply fir_cons_nonint; [exact H3|].
  apply fir_cons_nonint; [exact H4|].
  apply fir_cons_nonint; [exact H5|].
  constructor.
Qed.