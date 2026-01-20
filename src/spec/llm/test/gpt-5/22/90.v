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

Parameter v_true v_false v_none v_zero v_neg10 v_str v_empty_list v_empty_dict v_real1 v_real2 : Any.
Parameter z0 zneg10 : int.
Axiom isInt_v_zero : IsInt v_zero z0.
Axiom isInt_v_neg10 : IsInt v_neg10 zneg10.
Axiom nonint_v_true : forall n, ~ IsInt v_true n.
Axiom nonint_v_false : forall n, ~ IsInt v_false n.
Axiom nonint_v_none : forall n, ~ IsInt v_none n.
Axiom nonint_v_str : forall n, ~ IsInt v_str n.
Axiom nonint_v_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom nonint_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom nonint_v_real1 : forall n, ~ IsInt v_real1 n.
Axiom nonint_v_real2 : forall n, ~ IsInt v_real2 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_zero; v_neg10; v_str; v_empty_list; v_empty_dict; v_real1; v_real2]
    [z0; zneg10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_v_true|].
  eapply fir_cons_nonint; [apply nonint_v_false|].
  eapply fir_cons_nonint; [apply nonint_v_none|].
  eapply fir_cons_int; [apply isInt_v_zero|].
  eapply fir_cons_int; [apply isInt_v_neg10|].
  eapply fir_cons_nonint; [apply nonint_v_str|].
  eapply fir_cons_nonint; [apply nonint_v_empty_list|].
  eapply fir_cons_nonint; [apply nonint_v_empty_dict|].
  eapply fir_cons_nonint; [apply nonint_v_real1|].
  eapply fir_cons_nonint; [apply nonint_v_real2|].
  constructor.
Qed.