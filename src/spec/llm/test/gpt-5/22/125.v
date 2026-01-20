Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
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

Example test_case_new :
  forall a b c d e f,
    IsInt a 1%Z ->
    (forall n, ~ IsInt b n) ->
    (forall n, ~ IsInt c n) ->
    (forall n, ~ IsInt d n) ->
    IsInt e 9%Z ->
    (forall n, ~ IsInt f n) ->
    filter_integers_spec [a; b; c; d; e; f] [1%Z; 9%Z].
Proof.
  intros a b c d e f Ha Hb Hc Hd He Hf.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact Ha |].
  eapply fir_cons_nonint; [exact Hb |].
  eapply fir_cons_nonint; [exact Hc |].
  eapply fir_cons_nonint; [exact Hd |].
  eapply fir_cons_int; [exact He |].
  eapply fir_cons_nonint; [exact Hf |].
  constructor.
Qed.