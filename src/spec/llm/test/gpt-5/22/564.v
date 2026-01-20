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

Parameters a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Any.
Axiom H_nint_a0 : forall n:int, ~ IsInt a0 n.
Axiom H_a1_2 : IsInt a1 2%Z.
Axiom H_a2_m1 : IsInt a2 (-1)%Z.
Axiom H_nint_a3 : forall n:int, ~ IsInt a3 n.
Axiom H_nint_a4 : forall n:int, ~ IsInt a4 n.
Axiom H_nint_a5 : forall n:int, ~ IsInt a5 n.
Axiom H_nint_a6 : forall n:int, ~ IsInt a6 n.
Axiom H_nint_a7 : forall n:int, ~ IsInt a7 n.
Axiom H_a8_1 : IsInt a8 1%Z.
Axiom H_nint_a9 : forall n:int, ~ IsInt a9 n.

Example test_case_nested: filter_integers_spec [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] [2%Z; (-1)%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_nint_a0|].
  eapply fir_cons_int with (n := 2%Z); [apply H_a1_2|].
  eapply fir_cons_int with (n := (-1)%Z); [apply H_a2_m1|].
  eapply fir_cons_nonint; [apply H_nint_a3|].
  eapply fir_cons_nonint; [apply H_nint_a4|].
  eapply fir_cons_nonint; [apply H_nint_a5|].
  eapply fir_cons_nonint; [apply H_nint_a6|].
  eapply fir_cons_nonint; [apply H_nint_a7|].
  eapply fir_cons_int with (n := 1%Z); [apply H_a8_1|].
  eapply fir_cons_nonint; [apply H_nint_a9|].
  apply fir_nil.
Qed.