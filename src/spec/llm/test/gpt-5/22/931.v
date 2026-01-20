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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v10_is_int : IsInt v10 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.

Example test_case_filter_integers: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is_int|].
  eapply fir_cons_nonint; [apply v2_nonint|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_nonint; [apply v4_nonint|].
  eapply fir_cons_nonint; [apply v5_nonint|].
  eapply fir_cons_nonint; [apply v6_nonint|].
  eapply fir_cons_nonint; [apply v7_nonint|].
  eapply fir_cons_nonint; [apply v8_nonint|].
  eapply fir_cons_nonint; [apply v9_nonint|].
  eapply fir_cons_int; [apply v10_is_int|].
  constructor.
Qed.