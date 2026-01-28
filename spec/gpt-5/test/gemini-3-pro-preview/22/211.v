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

Parameter l1 l2 l3 l4 l5 : Any.
Axiom not_int_l1 : forall n, ~ IsInt l1 n.
Axiom not_int_l2 : forall n, ~ IsInt l2 n.
Axiom not_int_l3 : forall n, ~ IsInt l3 n.
Axiom not_int_l4 : forall n, ~ IsInt l4 n.
Axiom not_int_l5 : forall n, ~ IsInt l5 n.

Example test_filter_integers_lists : filter_integers_spec [l1; l2; l3; l4; l5] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_l1.
  apply fir_cons_nonint. apply not_int_l2.
  apply fir_cons_nonint. apply not_int_l3.
  apply fir_cons_nonint. apply not_int_l4.
  apply fir_cons_nonint. apply not_int_l5.
  apply fir_nil.
Qed.