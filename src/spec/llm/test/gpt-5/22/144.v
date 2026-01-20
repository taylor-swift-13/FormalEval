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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : Any.
Axiom v1_nonint : forall n, ~ IsInt v1 n.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom isint_v5 : IsInt v5 5%Z.
Axiom isint_v6 : IsInt v6 (-7)%Z.
Axiom isint_v7 : IsInt v7 0%Z.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.
Axiom v10_nonint : forall n, ~ IsInt v10 n.
Axiom v11_nonint : forall n, ~ IsInt v11 n.
Axiom v12_nonint : forall n, ~ IsInt v12 n.
Axiom v13_nonint : forall n, ~ IsInt v13 n.
Axiom v14_nonint : forall n, ~ IsInt v14 n.
Axiom v15_nonint : forall n, ~ IsInt v15 n.
Axiom v16_nonint : forall n, ~ IsInt v16 n.
Axiom v17_nonint : forall n, ~ IsInt v17 n.

Example test_case_1:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v1_nonint|].
  eapply fir_cons_nonint; [apply v2_nonint|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_nonint; [apply v4_nonint|].
  eapply fir_cons_int; [apply isint_v5|].
  eapply fir_cons_int; [apply isint_v6|].
  eapply fir_cons_int; [apply isint_v7|].
  eapply fir_cons_nonint; [apply v8_nonint|].
  eapply fir_cons_nonint; [apply v9_nonint|].
  eapply fir_cons_nonint; [apply v10_nonint|].
  eapply fir_cons_nonint; [apply v11_nonint|].
  eapply fir_cons_nonint; [apply v12_nonint|].
  eapply fir_cons_nonint; [apply v13_nonint|].
  eapply fir_cons_nonint; [apply v14_nonint|].
  eapply fir_cons_nonint; [apply v15_nonint|].
  eapply fir_cons_nonint; [apply v16_nonint|].
  eapply fir_cons_nonint; [apply v17_nonint|].
  constructor.
Qed.