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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : Any.
Parameter n1 n2 n3 n4 n5 : int.

Axiom NonInt_a1 : forall n, ~ IsInt a1 n.
Axiom NonInt_a2 : forall n, ~ IsInt a2 n.
Axiom NonInt_a3 : forall n, ~ IsInt a3 n.
Axiom NonInt_a4 : forall n, ~ IsInt a4 n.
Axiom IsInt_a5 : IsInt a5 n1.
Axiom NonInt_a6 : forall n, ~ IsInt a6 n.
Axiom IsInt_a7 : IsInt a7 n2.
Axiom IsInt_a8 : IsInt a8 n3.
Axiom NonInt_a9 : forall n, ~ IsInt a9 n.
Axiom NonInt_a10 : forall n, ~ IsInt a10 n.
Axiom NonInt_a11 : forall n, ~ IsInt a11 n.
Axiom NonInt_a12 : forall n, ~ IsInt a12 n.
Axiom NonInt_a13 : forall n, ~ IsInt a13 n.
Axiom NonInt_a14 : forall n, ~ IsInt a14 n.
Axiom IsInt_a15 : IsInt a15 n4.
Axiom NonInt_a16 : forall n, ~ IsInt a16 n.
Axiom NonInt_a17 : forall n, ~ IsInt a17 n.
Axiom IsInt_a18 : IsInt a18 n5.
Axiom NonInt_a19 : forall n, ~ IsInt a19 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13; a14; a15; a16; a17; a18; a19] [n1; n2; n3; n4; n5].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint; [apply NonInt_a1 |].
  apply fir_cons_nonint; [apply NonInt_a2 |].
  apply fir_cons_nonint; [apply NonInt_a3 |].
  apply fir_cons_nonint; [apply NonInt_a4 |].
  apply (fir_cons_int a5 n1); [apply IsInt_a5 |].
  apply fir_cons_nonint; [apply NonInt_a6 |].
  apply (fir_cons_int a7 n2); [apply IsInt_a7 |].
  apply (fir_cons_int a8 n3); [apply IsInt_a8 |].
  apply fir_cons_nonint; [apply NonInt_a9 |].
  apply fir_cons_nonint; [apply NonInt_a10 |].
  apply fir_cons_nonint; [apply NonInt_a11 |].
  apply fir_cons_nonint; [apply NonInt_a12 |].
  apply fir_cons_nonint; [apply NonInt_a13 |].
  apply fir_cons_nonint; [apply NonInt_a14 |].
  apply (fir_cons_int a15 n4); [apply IsInt_a15 |].
  apply fir_cons_nonint; [apply NonInt_a16 |].
  apply fir_cons_nonint; [apply NonInt_a17 |].
  apply (fir_cons_int a18 n5); [apply IsInt_a18 |].
  apply fir_cons_nonint; [apply NonInt_a19 |].
  apply fir_nil.
Qed.