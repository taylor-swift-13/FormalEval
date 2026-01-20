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

Parameter a1 a33 a_nested_234 a4 a_empty_list a_list_7_8 a_str9_1 a_str9_2 a_dict a1_again : Any.
Parameter n1 n33 n4 n1_again : int.
Axiom IsInt_a1 : IsInt a1 n1.
Axiom IsInt_a33 : IsInt a33 n33.
Axiom IsInt_a4 : IsInt a4 n4.
Axiom IsInt_a1_again : IsInt a1_again n1_again.
Axiom NotInt_a_nested_234 : forall n, ~ IsInt a_nested_234 n.
Axiom NotInt_a_empty_list : forall n, ~ IsInt a_empty_list n.
Axiom NotInt_a_list_7_8 : forall n, ~ IsInt a_list_7_8 n.
Axiom NotInt_a_str9_1 : forall n, ~ IsInt a_str9_1 n.
Axiom NotInt_a_str9_2 : forall n, ~ IsInt a_str9_2 n.
Axiom NotInt_a_dict : forall n, ~ IsInt a_dict n.

Example test_case_nested_mixed:
  filter_integers_spec
    [a1; a33; a_nested_234; a4; a_empty_list; a_list_7_8; a_str9_1; a_str9_2; a_dict; a1_again]
    [n1; n33; n4; n1_again].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_int; [apply IsInt_a33|].
  eapply fir_cons_nonint; [apply NotInt_a_nested_234|].
  eapply fir_cons_int; [apply IsInt_a4|].
  eapply fir_cons_nonint; [apply NotInt_a_empty_list|].
  eapply fir_cons_nonint; [apply NotInt_a_list_7_8|].
  eapply fir_cons_nonint; [apply NotInt_a_str9_1|].
  eapply fir_cons_nonint; [apply NotInt_a_str9_2|].
  eapply fir_cons_nonint; [apply NotInt_a_dict|].
  eapply fir_cons_int; [apply IsInt_a1_again|].
  constructor.
Qed.