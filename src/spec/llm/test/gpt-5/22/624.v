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

Parameters a15 a23 a4 a56 aEmpty a7s aObj aStr9 : Any.
Parameters i15 i4 : int.
Axiom H_a15 : IsInt a15 i15.
Axiom H_a4 : IsInt a4 i4.
Axiom H_a23 : forall n, ~ IsInt a23 n.
Axiom H_a56 : forall n, ~ IsInt a56 n.
Axiom H_aEmpty : forall n, ~ IsInt aEmpty n.
Axiom H_a7s : forall n, ~ IsInt a7s n.
Axiom H_aObj : forall n, ~ IsInt aObj n.
Axiom H_aStr9 : forall n, ~ IsInt aStr9 n.

Example test_case_mixed: filter_integers_spec [a15; a23; a4; a56; aEmpty; a7s; aObj; aStr9] [i15; i4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H_a15|].
  eapply fir_cons_nonint; [exact H_a23|].
  eapply fir_cons_int; [exact H_a4|].
  eapply fir_cons_nonint; [exact H_a56|].
  eapply fir_cons_nonint; [exact H_aEmpty|].
  eapply fir_cons_nonint; [exact H_a7s|].
  eapply fir_cons_nonint; [exact H_aObj|].
  eapply fir_cons_nonint; [exact H_aStr9|].
  apply fir_nil.
Qed.