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

Parameter a_true a_false a_none a_zero a_minus_ten a_test a_empty_list a_empty_object a_float_3_14 : Any.
Parameter i0 i_minus10 : int.
Axiom IsInt_zero : IsInt a_zero i0.
Axiom IsInt_minus_ten : IsInt a_minus_ten i_minus10.
Axiom NonInt_true : forall n, ~ IsInt a_true n.
Axiom NonInt_false : forall n, ~ IsInt a_false n.
Axiom NonInt_none : forall n, ~ IsInt a_none n.
Axiom NonInt_test : forall n, ~ IsInt a_test n.
Axiom NonInt_empty_list : forall n, ~ IsInt a_empty_list n.
Axiom NonInt_empty_object : forall n, ~ IsInt a_empty_object n.
Axiom NonInt_float_3_14 : forall n, ~ IsInt a_float_3_14 n.

Example test_case_mixed: filter_integers_spec [a_true; a_false; a_none; a_zero; a_minus_ten; a_test; a_empty_list; a_empty_object; a_float_3_14; a_none] [i0; i_minus10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_true |].
  eapply fir_cons_nonint; [apply NonInt_false |].
  eapply fir_cons_nonint; [apply NonInt_none |].
  eapply fir_cons_int; [apply IsInt_zero |].
  eapply fir_cons_int; [apply IsInt_minus_ten |].
  eapply fir_cons_nonint; [apply NonInt_test |].
  eapply fir_cons_nonint; [apply NonInt_empty_list |].
  eapply fir_cons_nonint; [apply NonInt_empty_object |].
  eapply fir_cons_nonint; [apply NonInt_float_3_14 |].
  eapply fir_cons_nonint; [apply NonInt_none |].
  constructor.
Qed.