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

Parameters v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom v1_isint : IsInt v1 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_isint : IsInt v4 8%Z.
Axiom v5_isint : IsInt v5 1%Z.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 8%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_isint|].
  eapply fir_cons_nonint; [apply v2_nonint|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_int; [apply v4_isint|].
  eapply fir_cons_int; [apply v5_isint|].
  eapply fir_cons_nonint; [apply v6_nonint|].
  eapply fir_cons_nonint; [apply v7_nonint|].
  constructor.
Qed.