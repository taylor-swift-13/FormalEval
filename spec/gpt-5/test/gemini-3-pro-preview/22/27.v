Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter from_R : R -> Any.
Axiom not_int_R : forall r n, ~ IsInt (from_R r) n.

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

Example test_filter_integers : filter_integers_spec 
  [from_R 78.61928819331277%R; from_R (-6.77509560458482%R); from_R (-16.107923403329096%R); from_R (-80.34678514569492%R)] 
  [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_R.
  apply fir_cons_nonint. apply not_int_R.
  apply fir_cons_nonint. apply not_int_R.
  apply fir_cons_nonint. apply not_int_R.
  apply fir_nil.
Qed.