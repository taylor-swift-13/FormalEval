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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Axiom v1_int : IsInt v1 2%Z.
Axiom v2_non : forall n, ~ IsInt v2 n.
Axiom v3_non : forall n, ~ IsInt v3 n.
Axiom v4_int : IsInt v4 5%Z.
Axiom v5_non : forall n, ~ IsInt v5 n.
Axiom v6_non : forall n, ~ IsInt v6 n.
Axiom v7_non : forall n, ~ IsInt v7 n.
Axiom v8_non : forall n, ~ IsInt v8 n.
Axiom v9_int : IsInt v9 2%Z.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [2%Z; 5%Z; 2%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_int|].
  eapply fir_cons_nonint; [apply v2_non|].
  eapply fir_cons_nonint; [apply v3_non|].
  eapply fir_cons_int; [apply v4_int|].
  eapply fir_cons_nonint; [apply v5_non|].
  eapply fir_cons_nonint; [apply v6_non|].
  eapply fir_cons_nonint; [apply v7_non|].
  eapply fir_cons_nonint; [apply v8_non|].
  eapply fir_cons_int; [apply v9_int|].
  apply fir_nil.
Qed.