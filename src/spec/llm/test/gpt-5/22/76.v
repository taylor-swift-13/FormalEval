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

Parameter v2_7 v3_0 v1_8262900227722207 vn4_6 v1_5a v1_5b : Any.
Axiom v2_7_nonint : forall n, ~ IsInt v2_7 n.
Axiom v3_0_nonint : forall n, ~ IsInt v3_0 n.
Axiom v1_8262900227722207_nonint : forall n, ~ IsInt v1_8262900227722207 n.
Axiom vn4_6_nonint : forall n, ~ IsInt vn4_6 n.
Axiom v1_5a_nonint : forall n, ~ IsInt v1_5a n.
Axiom v1_5b_nonint : forall n, ~ IsInt v1_5b n.

Example test_case_new: filter_integers_spec [v2_7; v3_0; v1_8262900227722207; vn4_6; v1_5a; v1_5b] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v2_7_nonint|].
  eapply fir_cons_nonint; [apply v3_0_nonint|].
  eapply fir_cons_nonint; [apply v1_8262900227722207_nonint|].
  eapply fir_cons_nonint; [apply vn4_6_nonint|].
  eapply fir_cons_nonint; [apply v1_5a_nonint|].
  eapply fir_cons_nonint; [apply v1_5b_nonint|].
  constructor.
Qed.