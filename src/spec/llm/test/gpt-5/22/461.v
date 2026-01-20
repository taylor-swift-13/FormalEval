Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Any.

Axiom H_a1 : IsInt a1 1%Z.
Axiom H_a2 : IsInt a2 2%Z.
Axiom H_a3 : IsInt a3 3%Z.
Axiom H_a4_non : forall n, ~ IsInt a4 n.
Axiom H_a5_non : forall n, ~ IsInt a5 n.
Axiom H_a6 : IsInt a6 6%Z.
Axiom H_a7_non : forall n, ~ IsInt a7 n.
Axiom H_a8_non : forall n, ~ IsInt a8 n.
Axiom H_a9_non : forall n, ~ IsInt a9 n.
Axiom H_a10_non : forall n, ~ IsInt a10 n.
Axiom H_a11_non : forall n, ~ IsInt a11 n.
Axiom H_a12 : IsInt a12 3%Z.

Example test_case: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12] [1%Z; 2%Z; 3%Z; 6%Z; 3%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H_a1 |].
  eapply fir_cons_int; [exact H_a2 |].
  eapply fir_cons_int; [exact H_a3 |].
  eapply fir_cons_nonint; [exact H_a4_non |].
  eapply fir_cons_nonint; [exact H_a5_non |].
  eapply fir_cons_int; [exact H_a6 |].
  eapply fir_cons_nonint; [exact H_a7_non |].
  eapply fir_cons_nonint; [exact H_a8_non |].
  eapply fir_cons_nonint; [exact H_a9_non |].
  eapply fir_cons_nonint; [exact H_a10_non |].
  eapply fir_cons_nonint; [exact H_a11_non |].
  eapply fir_cons_int; [exact H_a12 |].
  apply fir_nil.
Qed.