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

Parameter v_l1 v_l2 v_l3 v_l4 v_l5 v_l6 v_l7 : Any.
Parameter v_m75 v_0a v_0b v_1a v_1b : Any.
Parameter n_m75 n_0 n_1 : int.

Axiom H_l1_non : forall n, ~ IsInt v_l1 n.
Axiom H_l2_non : forall n, ~ IsInt v_l2 n.
Axiom H_l3_non : forall n, ~ IsInt v_l3 n.
Axiom H_l4_non : forall n, ~ IsInt v_l4 n.
Axiom H_l5_non : forall n, ~ IsInt v_l5 n.
Axiom H_l6_non : forall n, ~ IsInt v_l6 n.
Axiom H_l7_non : forall n, ~ IsInt v_l7 n.

Axiom H_m75 : IsInt v_m75 n_m75.
Axiom H_0a : IsInt v_0a n_0.
Axiom H_0b : IsInt v_0b n_0.
Axiom H_1a : IsInt v_1a n_1.
Axiom H_1b : IsInt v_1b n_1.

Example test_case: filter_integers_spec
  [v_l1; v_m75; v_0a; v_l2; v_l3; v_l4; v_l5; v_l6; v_0b; v_1a; v_1b; v_l7]
  [n_m75; n_0; n_0; n_1; n_1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_l1_non|].
  eapply fir_cons_int; [apply H_m75|].
  eapply fir_cons_int; [apply H_0a|].
  eapply fir_cons_nonint; [apply H_l2_non|].
  eapply fir_cons_nonint; [apply H_l3_non|].
  eapply fir_cons_nonint; [apply H_l4_non|].
  eapply fir_cons_nonint; [apply H_l5_non|].
  eapply fir_cons_nonint; [apply H_l6_non|].
  eapply fir_cons_int; [apply H_0b|].
  eapply fir_cons_int; [apply H_1a|].
  eapply fir_cons_int; [apply H_1b|].
  eapply fir_cons_nonint; [apply H_l7_non|].
  constructor.
Qed.