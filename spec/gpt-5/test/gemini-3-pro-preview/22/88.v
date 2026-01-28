Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter from_R : R -> Any.
Axiom R_not_int : forall r n, ~ IsInt (from_R r) n.

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

Example test_filter_integers_floats : filter_integers_spec [from_R 1.5%R; from_R 3.0%R; from_R 1.5%R; from_R 61.76736727274371%R] [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [apply R_not_int | ]).
  apply fir_nil.
Qed.