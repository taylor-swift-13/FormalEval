Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter Any_of_R : R -> Any.
Axiom IsInt_Any_of_R_false : forall r n, ~ IsInt (Any_of_R r) n.

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

Example test_filter_integers_reals :
  filter_integers_spec
    [Any_of_R 1.5%R; Any_of_R 2.7%R; Any_of_R 3.0%R; Any_of_R (-51.08332919278058)%R; Any_of_R (-4.6)%R]
    [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply IsInt_Any_of_R_false.
  apply fir_cons_nonint. apply IsInt_Any_of_R_false.
  apply fir_cons_nonint. apply IsInt_Any_of_R_false.
  apply fir_cons_nonint. apply IsInt_Any_of_R_false.
  apply fir_cons_nonint. apply IsInt_Any_of_R_false.
  apply fir_nil.
Qed.