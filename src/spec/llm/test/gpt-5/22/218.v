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

Example test_case_nested_lists:
  forall a b c d,
    (forall n, ~ IsInt a n) ->
    (forall n, ~ IsInt b n) ->
    (forall n, ~ IsInt c n) ->
    (forall n, ~ IsInt d n) ->
    filter_integers_spec [a; b; c; d] [].
Proof.
  intros a b c d Ha Hb Hc Hd.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact Ha|].
  eapply fir_cons_nonint; [exact Hb|].
  eapply fir_cons_nonint; [exact Hc|].
  eapply fir_cons_nonint; [exact Hd|].
  constructor.
Qed.