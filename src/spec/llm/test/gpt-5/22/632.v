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

Parameter v_false v_none v_float v5 v_minus7 v0 v_str_a v_str_b v_empty_obj v_dict v_list_34 v_list_56_7 : Any.

Axiom NotInt_v_false : forall n, ~ IsInt v_false n.
Axiom NotInt_v_none : forall n, ~ IsInt v_none n.
Axiom NotInt_v_float : forall n, ~ IsInt v_float n.
Axiom IsInt_v5 : IsInt v5 (5%Z).
Axiom IsInt_v_minus7 : IsInt v_minus7 ((-7)%Z).
Axiom IsInt_v0 : IsInt v0 (0%Z).
Axiom NotInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NotInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NotInt_v_empty_obj : forall n, ~ IsInt v_empty_obj n.
Axiom NotInt_v_dict : forall n, ~ IsInt v_dict n.
Axiom NotInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NotInt_v_list_56_7 : forall n, ~ IsInt v_list_56_7 n.

Example test_case_mixed:
  filter_integers_spec
    [v_false; v_none; v_float; v5; v_minus7; v0; v_str_a; v_str_b; v_empty_obj; v_dict; v_list_34; v_list_56_7]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NotInt_v_false|].
  eapply fir_cons_nonint; [exact NotInt_v_none|].
  eapply fir_cons_nonint; [exact NotInt_v_float|].
  eapply fir_cons_int; [exact IsInt_v5|].
  eapply fir_cons_int; [exact IsInt_v_minus7|].
  eapply fir_cons_int; [exact IsInt_v0|].
  eapply fir_cons_nonint; [exact NotInt_v_str_a|].
  eapply fir_cons_nonint; [exact NotInt_v_str_b|].
  eapply fir_cons_nonint; [exact NotInt_v_empty_obj|].
  eapply fir_cons_nonint; [exact NotInt_v_dict|].
  eapply fir_cons_nonint; [exact NotInt_v_list_34|].
  eapply fir_cons_nonint; [exact NotInt_v_list_56_7|].
  constructor.
Qed.