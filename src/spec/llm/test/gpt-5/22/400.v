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

Parameters a0 a1 a2 a3 a4 a5 a6 a7 a8 : Any.
Axiom H1 : IsInt a1 1%Z.
Axiom H7 : IsInt a7 9%Z.
Axiom Hnon0 : forall n, ~ IsInt a0 n.
Axiom Hnon2 : forall n, ~ IsInt a2 n.
Axiom Hnon3 : forall n, ~ IsInt a3 n.
Axiom Hnon4 : forall n, ~ IsInt a4 n.
Axiom Hnon5 : forall n, ~ IsInt a5 n.
Axiom Hnon6 : forall n, ~ IsInt a6 n.
Axiom Hnon8 : forall n, ~ IsInt a8 n.

Example test_case_new:
  filter_integers_spec
    [a0; a1; a2; a3; a4; a5; a6; a7; a8]
    [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hnon0|].
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply Hnon2|].
  eapply fir_cons_nonint; [apply Hnon3|].
  eapply fir_cons_nonint; [apply Hnon4|].
  eapply fir_cons_nonint; [apply Hnon5|].
  eapply fir_cons_nonint; [apply Hnon6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_nonint; [apply Hnon8|].
  apply fir_nil.
Qed.