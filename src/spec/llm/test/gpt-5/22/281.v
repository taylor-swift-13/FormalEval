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

Parameters a1 a2 a3 a4 a5 : Any.
Axiom a1_isint : IsInt a1 1%Z.
Axiom a2_nonint : forall n, ~ IsInt a2 n.
Axiom a3_nonint : forall n, ~ IsInt a3 n.
Axiom a4_nonint : forall n, ~ IsInt a4 n.
Axiom a5_isint : IsInt a5 3%Z.

Example test_case_1: filter_integers_spec [a1; a2; a3; a4; a5] [1%Z; 3%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (n := 1%Z).
  - apply a1_isint.
  - eapply fir_cons_nonint; [apply a2_nonint|].
    eapply fir_cons_nonint; [apply a3_nonint|].
    eapply fir_cons_nonint; [apply a4_nonint|].
    eapply fir_cons_int with (n := 3%Z).
    + apply a5_isint.
    + constructor.
Qed.