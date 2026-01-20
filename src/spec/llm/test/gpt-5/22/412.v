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

Parameter a_empty1 : Any.
Parameter a_88 : Any.
Parameter a_empty2 : Any.
Parameter a_list5_1 : Any.
Parameter a_bools : Any.
Parameter a_list88_1 : Any.
Parameter a_9_1 : Any.
Parameter a_9_2 : Any.
Parameter a_list5_2 : Any.
Parameter a_list88_2 : Any.
Parameter a_list88_3 : Any.
Parameter a_list5_3 : Any.
Parameter a_empty3 : Any.

Parameter i88 : int.
Parameter i9 : int.

Notation "88%Z" := i88.
Notation "9%Z" := i9.

Axiom IsInt_a_88_i88 : IsInt a_88 i88.
Axiom IsInt_a_9_1_i9 : IsInt a_9_1 i9.
Axiom IsInt_a_9_2_i9 : IsInt a_9_2 i9.

Axiom NotInt_a_empty1 : forall n, ~ IsInt a_empty1 n.
Axiom NotInt_a_empty2 : forall n, ~ IsInt a_empty2 n.
Axiom NotInt_a_list5_1 : forall n, ~ IsInt a_list5_1 n.
Axiom NotInt_a_bools : forall n, ~ IsInt a_bools n.
Axiom NotInt_a_list88_1 : forall n, ~ IsInt a_list88_1 n.
Axiom NotInt_a_list5_2 : forall n, ~ IsInt a_list5_2 n.
Axiom NotInt_a_list88_2 : forall n, ~ IsInt a_list88_2 n.
Axiom NotInt_a_list88_3 : forall n, ~ IsInt a_list88_3 n.
Axiom NotInt_a_list5_3 : forall n, ~ IsInt a_list5_3 n.
Axiom NotInt_a_empty3 : forall n, ~ IsInt a_empty3 n.

Example test_case_new:
  filter_integers_spec
    [a_empty1; a_88; a_empty2; a_list5_1; a_bools; a_list88_1; a_9_1; a_9_2; a_list5_2; a_list88_2; a_list88_3; a_list5_3; a_empty3]
    [88%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NotInt_a_empty1 |].
  eapply fir_cons_int; [apply IsInt_a_88_i88 |].
  eapply fir_cons_nonint; [apply NotInt_a_empty2 |].
  eapply fir_cons_nonint; [apply NotInt_a_list5_1 |].
  eapply fir_cons_nonint; [apply NotInt_a_bools |].
  eapply fir_cons_nonint; [apply NotInt_a_list88_1 |].
  eapply fir_cons_int; [apply IsInt_a_9_1_i9 |].
  eapply fir_cons_int; [apply IsInt_a_9_2_i9 |].
  eapply fir_cons_nonint; [apply NotInt_a_list5_2 |].
  eapply fir_cons_nonint; [apply NotInt_a_list88_2 |].
  eapply fir_cons_nonint; [apply NotInt_a_list88_3 |].
  eapply fir_cons_nonint; [apply NotInt_a_list5_3 |].
  eapply fir_cons_nonint; [apply NotInt_a_empty3 |].
  apply fir_nil.
Qed.