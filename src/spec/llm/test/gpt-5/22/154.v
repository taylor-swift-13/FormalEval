Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.
Parameters z2 z3 z6 : int.

Axiom v1_is : IsInt v1 z2.
Axiom v2_non : forall n, ~ IsInt v2 n.
Axiom v3_is : IsInt v3 z2.
Axiom v4_is : IsInt v4 z3.
Axiom v5_non : forall n, ~ IsInt v5 n.
Axiom v6_is : IsInt v6 z3.
Axiom v7_non : forall n, ~ IsInt v7 n.
Axiom v8_is : IsInt v8 z6.
Axiom v9_non : forall n, ~ IsInt v9 n.
Axiom v10_non : forall n, ~ IsInt v10 n.
Axiom v11_non : forall n, ~ IsInt v11 n.
Axiom v12_non : forall n, ~ IsInt v12 n.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12]
    [z2; z2; z3; z3; z6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is|].
  eapply fir_cons_nonint; [apply v2_non|].
  eapply fir_cons_int; [apply v3_is|].
  eapply fir_cons_int; [apply v4_is|].
  eapply fir_cons_nonint; [apply v5_non|].
  eapply fir_cons_int; [apply v6_is|].
  eapply fir_cons_nonint; [apply v7_non|].
  eapply fir_cons_int; [apply v8_is|].
  eapply fir_cons_nonint; [apply v9_non|].
  eapply fir_cons_nonint; [apply v10_non|].
  eapply fir_cons_nonint; [apply v11_non|].
  eapply fir_cons_nonint; [apply v12_non|].
  constructor.
Qed.