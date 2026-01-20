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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 : Any.
Axiom HIsInt1 : IsInt a1 1%Z.
Axiom HNonInt2 : forall n, ~ IsInt a2 n.
Axiom HIsInt3 : IsInt a3 29%Z.
Axiom HNonInt4 : forall n, ~ IsInt a4 n.
Axiom HNonInt5 : forall n, ~ IsInt a5 n.
Axiom HNonInt6 : forall n, ~ IsInt a6 n.
Axiom HNonInt7 : forall n, ~ IsInt a7 n.
Axiom HNonInt8 : forall n, ~ IsInt a8 n.
Axiom HIsInt9 : IsInt a9 1%Z.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9] [1%Z; 29%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply HIsInt1|].
  eapply fir_cons_nonint; [apply HNonInt2|].
  eapply fir_cons_int; [apply HIsInt3|].
  eapply fir_cons_nonint; [apply HNonInt4|].
  eapply fir_cons_nonint; [apply HNonInt5|].
  eapply fir_cons_nonint; [apply HNonInt6|].
  eapply fir_cons_nonint; [apply HNonInt7|].
  eapply fir_cons_nonint; [apply HNonInt8|].
  eapply fir_cons_int; [apply HIsInt9|].
  constructor.
Qed.