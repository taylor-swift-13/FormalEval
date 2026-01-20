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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.
Parameter n2 n3 n10 : int.
Axiom IsInt_a1 : IsInt a1 n2.
Axiom IsInt_a2 : IsInt a2 n3.
Axiom NonInt_a3 : forall n, ~ IsInt a3 n.
Axiom NonInt_a4 : forall n, ~ IsInt a4 n.
Axiom NonInt_a5 : forall n, ~ IsInt a5 n.
Axiom NonInt_a6 : forall n, ~ IsInt a6 n.
Axiom NonInt_a7 : forall n, ~ IsInt a7 n.
Axiom NonInt_a8 : forall n, ~ IsInt a8 n.
Axiom NonInt_a9 : forall n, ~ IsInt a9 n.
Axiom IsInt_a10 : IsInt a10 n10.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [n2; n3; n10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1 |].
  eapply fir_cons_int; [apply IsInt_a2 |].
  eapply fir_cons_nonint; [apply NonInt_a3 |].
  eapply fir_cons_nonint; [apply NonInt_a4 |].
  eapply fir_cons_nonint; [apply NonInt_a5 |].
  eapply fir_cons_nonint; [apply NonInt_a6 |].
  eapply fir_cons_nonint; [apply NonInt_a7 |].
  eapply fir_cons_nonint; [apply NonInt_a8 |].
  eapply fir_cons_nonint; [apply NonInt_a9 |].
  eapply fir_cons_int; [apply IsInt_a10 |].
  apply fir_nil.
Qed.