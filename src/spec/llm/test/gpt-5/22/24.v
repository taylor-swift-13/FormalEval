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

Parameter a_true a_false a_none a_0 a_neg10 a_test a_emptylist a_dict a_3p14 : Any.
Parameter n0 nneg10 : int.
Axiom IsInt_a_0 : IsInt a_0 n0.
Axiom IsInt_a_neg10 : IsInt a_neg10 nneg10.
Axiom NonInt_a_true : forall n, ~ IsInt a_true n.
Axiom NonInt_a_false : forall n, ~ IsInt a_false n.
Axiom NonInt_a_none : forall n, ~ IsInt a_none n.
Axiom NonInt_a_test : forall n, ~ IsInt a_test n.
Axiom NonInt_a_emptylist : forall n, ~ IsInt a_emptylist n.
Axiom NonInt_a_dict : forall n, ~ IsInt a_dict n.
Axiom NonInt_a_3p14 : forall n, ~ IsInt a_3p14 n.

Example test_case_mixed:
  filter_integers_spec
    [a_true; a_false; a_none; a_0; a_neg10; a_test; a_emptylist; a_dict; a_3p14]
    [n0; nneg10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_a_true|].
  eapply fir_cons_nonint; [apply NonInt_a_false|].
  eapply fir_cons_nonint; [apply NonInt_a_none|].
  eapply fir_cons_int; [apply IsInt_a_0|].
  eapply fir_cons_int; [apply IsInt_a_neg10|].
  eapply fir_cons_nonint; [apply NonInt_a_test|].
  eapply fir_cons_nonint; [apply NonInt_a_emptylist|].
  eapply fir_cons_nonint; [apply NonInt_a_dict|].
  eapply fir_cons_nonint; [apply NonInt_a_3p14|].
  constructor.
Qed.