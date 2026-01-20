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

Parameter v_true : Any.
Parameter v_false : Any.
Parameter v_none : Any.
Parameter v_zero : Any.
Parameter v_neg10 : Any.
Parameter v_test1 : Any.
Parameter v_empty_list : Any.
Parameter v_empty_dict : Any.
Parameter v_pi : Any.
Parameter v_test2 : Any.

Parameter n_zero : int.
Parameter n_neg10 : int.

Axiom axiom_isInt_zero : IsInt v_zero n_zero.
Axiom axiom_isInt_neg10 : IsInt v_neg10 n_neg10.

Axiom axiom_nonint_true : forall n, ~ IsInt v_true n.
Axiom axiom_nonint_false : forall n, ~ IsInt v_false n.
Axiom axiom_nonint_none : forall n, ~ IsInt v_none n.
Axiom axiom_nonint_test1 : forall n, ~ IsInt v_test1 n.
Axiom axiom_nonint_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom axiom_nonint_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom axiom_nonint_pi : forall n, ~ IsInt v_pi n.
Axiom axiom_nonint_test2 : forall n, ~ IsInt v_test2 n.

Example test_case_mixed: filter_integers_spec
  [v_true; v_false; v_none; v_zero; v_neg10; v_test1; v_empty_list; v_empty_dict; v_pi; v_test2]
  [n_zero; n_neg10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply axiom_nonint_true |].
  eapply fir_cons_nonint; [apply axiom_nonint_false |].
  eapply fir_cons_nonint; [apply axiom_nonint_none |].
  eapply fir_cons_int; [apply axiom_isInt_zero |].
  eapply fir_cons_int; [apply axiom_isInt_neg10 |].
  eapply fir_cons_nonint; [apply axiom_nonint_test1 |].
  eapply fir_cons_nonint; [apply axiom_nonint_empty_list |].
  eapply fir_cons_nonint; [apply axiom_nonint_empty_dict |].
  eapply fir_cons_nonint; [apply axiom_nonint_pi |].
  eapply fir_cons_nonint; [apply axiom_nonint_test2 |].
  apply fir_nil.
Qed.