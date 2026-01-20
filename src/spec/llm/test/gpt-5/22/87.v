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

Parameter v_hello v_how1 v_world v_empty v_ho_2w v_worldhow v_test v_you v_how2 : Any.
Axiom v_hello_nonint : forall n, ~ IsInt v_hello n.
Axiom v_how1_nonint : forall n, ~ IsInt v_how1 n.
Axiom v_world_nonint : forall n, ~ IsInt v_world n.
Axiom v_empty_nonint : forall n, ~ IsInt v_empty n.
Axiom v_ho_2w_nonint : forall n, ~ IsInt v_ho_2w n.
Axiom v_worldhow_nonint : forall n, ~ IsInt v_worldhow n.
Axiom v_test_nonint : forall n, ~ IsInt v_test n.
Axiom v_you_nonint : forall n, ~ IsInt v_you n.
Axiom v_how2_nonint : forall n, ~ IsInt v_how2 n.

Example test_case_strings:
  filter_integers_spec
    [v_hello; v_how1; v_world; v_empty; v_ho_2w; v_worldhow; v_test; v_you; v_how2]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_hello_nonint|].
  eapply fir_cons_nonint; [apply v_how1_nonint|].
  eapply fir_cons_nonint; [apply v_world_nonint|].
  eapply fir_cons_nonint; [apply v_empty_nonint|].
  eapply fir_cons_nonint; [apply v_ho_2w_nonint|].
  eapply fir_cons_nonint; [apply v_worldhow_nonint|].
  eapply fir_cons_nonint; [apply v_test_nonint|].
  eapply fir_cons_nonint; [apply v_you_nonint|].
  eapply fir_cons_nonint; [apply v_how2_nonint|].
  constructor.
Qed.