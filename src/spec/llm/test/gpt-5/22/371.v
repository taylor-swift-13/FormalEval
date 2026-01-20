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

Parameter v0 v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameter n0 n1 n2 n3 : int.
Axiom v0_is_int : IsInt v0 n0.
Axiom v1_is_int : IsInt v1 n1.
Axiom v2_is_int : IsInt v2 n2.
Axiom v4_is_int : IsInt v4 n3.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_not_int : forall n, ~ IsInt v6 n.
Axiom v7_not_int : forall n, ~ IsInt v7 n.
Axiom v8_not_int : forall n, ~ IsInt v8 n.

Example test_case_mixed: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8] [n0; n1; n2; n3].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v0_is_int|].
  eapply fir_cons_int; [apply v1_is_int|].
  eapply fir_cons_int; [apply v2_is_int|].
  eapply fir_cons_nonint; [apply v3_not_int|].
  eapply fir_cons_int; [apply v4_is_int|].
  eapply fir_cons_nonint; [apply v5_not_int|].
  eapply fir_cons_nonint; [apply v6_not_int|].
  eapply fir_cons_nonint; [apply v7_not_int|].
  eapply fir_cons_nonint; [apply v8_not_int|].
  constructor.
Qed.