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

Example test_case_single_integer:
  forall a b c d e v n,
  (forall m, ~ IsInt a m) ->
  (forall m, ~ IsInt b m) ->
  (forall m, ~ IsInt c m) ->
  (forall m, ~ IsInt d m) ->
  (forall m, ~ IsInt e m) ->
  IsInt v n ->
  filter_integers_spec [a; b; c; d; e; v] [n].
Proof.
  unfold filter_integers_spec.
  intros a b c d e v n Ha Hb Hc Hd He Hv.
  eapply fir_cons_nonint; [exact Ha|].
  eapply fir_cons_nonint; [exact Hb|].
  eapply fir_cons_nonint; [exact Hc|].
  eapply fir_cons_nonint; [exact Hd|].
  eapply fir_cons_nonint; [exact He|].
  eapply fir_cons_int; [exact Hv|].
  constructor.
Qed.