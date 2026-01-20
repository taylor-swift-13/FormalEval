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

Parameters a1 a2 a3 a4 a5 a6 a7 : Any.
Parameters n1 n2 : int.
Axiom A1_int : IsInt a1 n1.
Axiom A2_nonint : forall n, ~ IsInt a2 n.
Axiom A3_nonint : forall n, ~ IsInt a3 n.
Axiom A4_nonint : forall n, ~ IsInt a4 n.
Axiom A5_nonint : forall n, ~ IsInt a5 n.
Axiom A6_int : IsInt a6 n2.
Axiom A7_nonint : forall n, ~ IsInt a7 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7] [n1; n2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply A1_int|].
  eapply fir_cons_nonint; [apply A2_nonint|].
  eapply fir_cons_nonint; [apply A3_nonint|].
  eapply fir_cons_nonint; [apply A4_nonint|].
  eapply fir_cons_nonint; [apply A5_nonint|].
  eapply fir_cons_int; [apply A6_int|].
  eapply fir_cons_nonint; [apply A7_nonint|].
  constructor.
Qed.