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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.

Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_is_int : IsInt v4 8%Z.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_not_int : forall n, ~ IsInt v6 n.
Axiom v7_is_int : IsInt v7 9%Z.
Axiom v8_is_int : IsInt v8 9%Z.
Axiom v9_not_int : forall n, ~ IsInt v9 n.
Axiom v10_not_int : forall n, ~ IsInt v10 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is_int|].
  eapply fir_cons_nonint; [apply v2_not_int|].
  eapply fir_cons_nonint; [apply v3_not_int|].
  eapply fir_cons_int; [apply v4_is_int|].
  eapply fir_cons_nonint; [apply v5_not_int|].
  eapply fir_cons_nonint; [apply v6_not_int|].
  eapply fir_cons_int; [apply v7_is_int|].
  eapply fir_cons_int; [apply v8_is_int|].
  eapply fir_cons_nonint; [apply v9_not_int|].
  eapply fir_cons_nonint; [apply v10_not_int|].
  constructor.
Qed.