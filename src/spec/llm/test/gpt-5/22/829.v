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

Parameters a1 a2 a3 a4 a5 a6 : Any.
Axioms nonint_a1 : forall n, ~ IsInt a1 n.
Axioms nonint_a2 : forall n, ~ IsInt a2 n.
Axioms nonint_a3 : forall n, ~ IsInt a3 n.
Axioms nonint_a4 : forall n, ~ IsInt a4 n.
Axioms nonint_a5 : forall n, ~ IsInt a5 n.
Axioms nonint_a6 : forall n, ~ IsInt a6 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [ exact nonint_a1 |].
  eapply fir_cons_nonint; [ exact nonint_a2 |].
  eapply fir_cons_nonint; [ exact nonint_a3 |].
  eapply fir_cons_nonint; [ exact nonint_a4 |].
  eapply fir_cons_nonint; [ exact nonint_a5 |].
  eapply fir_cons_nonint; [ exact nonint_a6 |].
  constructor.
Qed.