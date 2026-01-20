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

Parameter a0 a2 a3 a6 a_r55 a_seven a_sveven a_88 a_four : Any.
Parameter n0 n2 n3 n6 : int.
Axiom IsInt_a0 : IsInt a0 n0.
Axiom IsInt_a2 : IsInt a2 n2.
Axiom IsInt_a3 : IsInt a3 n3.
Axiom IsInt_a6 : IsInt a6 n6.
Axiom NonInt_a_r55 : forall n, ~ IsInt a_r55 n.
Axiom NonInt_a_seven : forall n, ~ IsInt a_seven n.
Axiom NonInt_a_sveven : forall n, ~ IsInt a_sveven n.
Axiom NonInt_a_88 : forall n, ~ IsInt a_88 n.
Axiom NonInt_a_four : forall n, ~ IsInt a_four n.

Example test_case_mixed: filter_integers_spec [a0; a2; a3; a_r55; a6; a_seven; a_sveven; a_88; a_four] [n0; n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a0 |].
  eapply fir_cons_int; [apply IsInt_a2 |].
  eapply fir_cons_int; [apply IsInt_a3 |].
  eapply fir_cons_nonint; [apply NonInt_a_r55 |].
  eapply fir_cons_int; [apply IsInt_a6 |].
  eapply fir_cons_nonint; [apply NonInt_a_seven |].
  eapply fir_cons_nonint; [apply NonInt_a_sveven |].
  eapply fir_cons_nonint; [apply NonInt_a_88 |].
  eapply fir_cons_nonint; [apply NonInt_a_four |].
  apply fir_nil.
Qed.