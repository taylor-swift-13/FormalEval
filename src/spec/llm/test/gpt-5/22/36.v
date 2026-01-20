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

Parameter a_2_5R : Any.
Parameter a_4_6R : Any.
Parameter a_7_8R : Any.
Parameter a_abc : Any.
Parameter a_emptyset : Any.
Parameter a_emptylist : Any.

Axiom NotInt_a_2_5R : forall n, ~ IsInt a_2_5R n.
Axiom NotInt_a_4_6R : forall n, ~ IsInt a_4_6R n.
Axiom NotInt_a_7_8R : forall n, ~ IsInt a_7_8R n.
Axiom NotInt_a_abc : forall n, ~ IsInt a_abc n.
Axiom NotInt_a_emptyset : forall n, ~ IsInt a_emptyset n.
Axiom NotInt_a_emptylist : forall n, ~ IsInt a_emptylist n.

Example test_case_nonints: filter_integers_spec [a_2_5R; a_4_6R; a_7_8R; a_abc; a_emptyset; a_emptylist; a_7_8R] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NotInt_a_2_5R |].
  eapply fir_cons_nonint; [apply NotInt_a_4_6R |].
  eapply fir_cons_nonint; [apply NotInt_a_7_8R |].
  eapply fir_cons_nonint; [apply NotInt_a_abc |].
  eapply fir_cons_nonint; [apply NotInt_a_emptyset |].
  eapply fir_cons_nonint; [apply NotInt_a_emptylist |].
  eapply fir_cons_nonint; [apply NotInt_a_7_8R |].
  constructor.
Qed.