Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

(* Parameters for the specific test case values *)
Parameter v_true : Any.
Parameter v_false : Any.
Parameter v_none : Any.
Parameter v_0 : Any.
Parameter v_neg10 : Any.
Parameter v_test : Any.
Parameter v_empty_list : Any.
Parameter v_empty_dict : Any.
Parameter v_pi : Any.

Parameter i_0 : int.
Parameter i_neg10 : int.

(* Axioms defining the properties of these values with respect to IsInt *)
Axiom not_int_true : forall n, ~ IsInt v_true n.
Axiom not_int_false : forall n, ~ IsInt v_false n.
Axiom not_int_none : forall n, ~ IsInt v_none n.
Axiom is_int_0 : IsInt v_0 i_0.
Axiom is_int_neg10 : IsInt v_neg10 i_neg10.
Axiom not_int_test : forall n, ~ IsInt v_test n.
Axiom not_int_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom not_int_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom not_int_pi : forall n, ~ IsInt v_pi n.

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

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v_true; v_false; v_none; v_0; v_neg10; v_test; v_empty_list; v_empty_dict; v_pi] 
    [i_0; i_neg10].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_true.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_none.
  apply fir_cons_int with (n := i_0). apply is_int_0.
  apply fir_cons_int with (n := i_neg10). apply is_int_neg10.
  apply fir_cons_nonint. apply not_int_test.
  apply fir_cons_nonint. apply not_int_empty_list.
  apply fir_cons_nonint. apply not_int_empty_dict.
  apply fir_cons_nonint. apply not_int_pi.
  apply fir_nil.
Qed.