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
Axiom v1_isint : IsInt v1 1%Z.
Axiom v2_isint : IsInt v2 2%Z.
Axiom v3_isint : IsInt v3 3%Z.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_isint : IsInt v6 6%Z.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.
Axiom v10_nonint : forall n, ~ IsInt v10 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1%Z; 2%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_isint |].
  eapply fir_cons_int; [apply v2_isint |].
  eapply fir_cons_int; [apply v3_isint |].
  eapply fir_cons_nonint; [apply v4_nonint |].
  eapply fir_cons_nonint; [apply v5_nonint |].
  eapply fir_cons_int; [apply v6_isint |].
  eapply fir_cons_nonint; [apply v7_nonint |].
  eapply fir_cons_nonint; [apply v8_nonint |].
  eapply fir_cons_nonint; [apply v9_nonint |].
  eapply fir_cons_nonint; [apply v10_nonint |].
  constructor.
Qed.