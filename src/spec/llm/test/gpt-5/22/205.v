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

Parameter a_l1 : Any.
Parameter a2 : Any.
Parameter a_l2 : Any.
Parameter a_l3 : Any.
Parameter a_l4 : Any.
Parameter a_l5 : Any.
Parameter a_l6 : Any.
Parameter a1 : Any.
Parameter a_l7 : Any.

Axiom IsInt_a2 : IsInt a2 2%Z.
Axiom IsInt_a1 : IsInt a1 1%Z.
Axiom NonInt_a_l1 : forall n, ~ IsInt a_l1 n.
Axiom NonInt_a_l2 : forall n, ~ IsInt a_l2 n.
Axiom NonInt_a_l3 : forall n, ~ IsInt a_l3 n.
Axiom NonInt_a_l4 : forall n, ~ IsInt a_l4 n.
Axiom NonInt_a_l5 : forall n, ~ IsInt a_l5 n.
Axiom NonInt_a_l6 : forall n, ~ IsInt a_l6 n.
Axiom NonInt_a_l7 : forall n, ~ IsInt a_l7 n.

Example test_case_mixed: filter_integers_spec [a_l1; a2; a_l2; a_l3; a_l4; a_l5; a_l6; a1; a_l7] [2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact NonInt_a_l1.
  eapply fir_cons_int. exact IsInt_a2.
  eapply fir_cons_nonint. exact NonInt_a_l2.
  eapply fir_cons_nonint. exact NonInt_a_l3.
  eapply fir_cons_nonint. exact NonInt_a_l4.
  eapply fir_cons_nonint. exact NonInt_a_l5.
  eapply fir_cons_nonint. exact NonInt_a_l6.
  eapply fir_cons_int. exact IsInt_a1.
  eapply fir_cons_nonint. exact NonInt_a_l7.
  apply fir_nil.
Qed.