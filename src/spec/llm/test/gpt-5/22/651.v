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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 : Any.
Axiom a1_is_int : IsInt a1 1%Z.
Axiom a2_nonint : forall n, ~ IsInt a2 n.
Axiom a3_nonint : forall n, ~ IsInt a3 n.
Axiom a4_nonint : forall n, ~ IsInt a4 n.
Axiom a5_nonint : forall n, ~ IsInt a5 n.
Axiom a6_nonint : forall n, ~ IsInt a6 n.
Axiom a7_nonint : forall n, ~ IsInt a7 n.
Axiom a8_is_int : IsInt a8 9%Z.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8] [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact a1_is_int|].
  eapply fir_cons_nonint; [exact a2_nonint|].
  eapply fir_cons_nonint; [exact a3_nonint|].
  eapply fir_cons_nonint; [exact a4_nonint|].
  eapply fir_cons_nonint; [exact a5_nonint|].
  eapply fir_cons_nonint; [exact a6_nonint|].
  eapply fir_cons_nonint; [exact a7_nonint|].
  eapply fir_cons_int; [exact a8_is_int|].
  apply fir_nil.
Qed.