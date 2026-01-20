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

Parameter a1 a2 a3 a4 a5 a6 : Any.
Parameter a1_isint : IsInt a1 1%Z.
Parameter a2_nonint : forall n, ~ IsInt a2 n.
Parameter a3_nonint : forall n, ~ IsInt a3 n.
Parameter a4_isint : IsInt a4 7%Z.
Parameter a5_nonint : forall n, ~ IsInt a5 n.
Parameter a6_isint : IsInt a6 1%Z.

Example test_case_nested: filter_integers_spec [a1; a2; a3; a4; a5; a6] [1%Z; 7%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply a1_isint|].
  eapply fir_cons_nonint; [apply a2_nonint|].
  eapply fir_cons_nonint; [apply a3_nonint|].
  eapply fir_cons_int; [apply a4_isint|].
  eapply fir_cons_nonint; [apply a5_nonint|].
  eapply fir_cons_int; [apply a6_isint|].
  apply fir_nil.
Qed.