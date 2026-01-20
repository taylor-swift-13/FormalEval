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

Parameter a1 a2 a3 a_four a_5_5 a6 a_seven a_9_0 : Any.
Parameter n1 n2 n3 n6 : int.
Axiom IsInt_a1 : IsInt a1 n1.
Axiom IsInt_a2 : IsInt a2 n2.
Axiom IsInt_a3 : IsInt a3 n3.
Axiom IsInt_a6 : IsInt a6 n6.
Axiom nonint_four : forall n, ~ IsInt a_four n.
Axiom nonint_5_5 : forall n, ~ IsInt a_5_5 n.
Axiom nonint_seven : forall n, ~ IsInt a_seven n.
Axiom nonint_9_0 : forall n, ~ IsInt a_9_0 n.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a_four; a_5_5; a6; a_seven; a_9_0] [n1; n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_a1|].
  eapply fir_cons_int; [exact IsInt_a2|].
  eapply fir_cons_int; [exact IsInt_a3|].
  eapply fir_cons_nonint; [exact nonint_four|].
  eapply fir_cons_nonint; [exact nonint_5_5|].
  eapply fir_cons_int; [exact IsInt_a6|].
  eapply fir_cons_nonint; [exact nonint_seven|].
  eapply fir_cons_nonint; [exact nonint_9_0|].
  constructor.
Qed.