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

Parameter v1 v10 v_2_3 v_neg82_4 v_5_6 v_7_2_a v_7_2_b v9 : Any.
Axiom v1_isint : IsInt v1 1%Z.
Axiom v10_isint : IsInt v10 10%Z.
Axiom v9_isint : IsInt v9 9%Z.
Axiom v_2_3_nonint : forall n, ~ IsInt v_2_3 n.
Axiom v_neg82_4_nonint : forall n, ~ IsInt v_neg82_4 n.
Axiom v_5_6_nonint : forall n, ~ IsInt v_5_6 n.
Axiom v_7_2_a_nonint : forall n, ~ IsInt v_7_2_a n.
Axiom v_7_2_b_nonint : forall n, ~ IsInt v_7_2_b n.

Example test_case_empty: filter_integers_spec [v1; v10; v_2_3; v_neg82_4; v_5_6; v_7_2_a; v_7_2_b; v9] [1%Z; 10%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_isint|].
  eapply fir_cons_int; [apply v10_isint|].
  eapply fir_cons_nonint; [apply v_2_3_nonint|].
  eapply fir_cons_nonint; [apply v_neg82_4_nonint|].
  eapply fir_cons_nonint; [apply v_5_6_nonint|].
  eapply fir_cons_nonint; [apply v_7_2_a_nonint|].
  eapply fir_cons_nonint; [apply v_7_2_b_nonint|].
  eapply fir_cons_int; [apply v9_isint|].
  apply fir_nil.
Qed.