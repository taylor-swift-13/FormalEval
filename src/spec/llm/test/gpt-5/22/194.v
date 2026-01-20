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

Parameter a2 a_l1 a_lA1 a_lB a_lA2 a_lA3 a_lC a9 a1 : Any.
Parameter i2 i9 i1 : int.

Axiom IsInt_a2 : IsInt a2 i2.
Axiom IsInt_a9 : IsInt a9 i9.
Axiom IsInt_a1 : IsInt a1 i1.

Axiom NonInt_a_l1 : forall n, ~ IsInt a_l1 n.
Axiom NonInt_a_lA1 : forall n, ~ IsInt a_lA1 n.
Axiom NonInt_a_lB : forall n, ~ IsInt a_lB n.
Axiom NonInt_a_lA2 : forall n, ~ IsInt a_lA2 n.
Axiom NonInt_a_lA3 : forall n, ~ IsInt a_lA3 n.
Axiom NonInt_a_lC : forall n, ~ IsInt a_lC n.

Example test_case_new:
  filter_integers_spec
    [a2; a_l1; a_lA1; a_lB; a_lA2; a_lA3; a_lC; a9; a1]
    [i2; i9; i1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_a2|].
  eapply fir_cons_nonint; [exact NonInt_a_l1|].
  eapply fir_cons_nonint; [exact NonInt_a_lA1|].
  eapply fir_cons_nonint; [exact NonInt_a_lB|].
  eapply fir_cons_nonint; [exact NonInt_a_lA2|].
  eapply fir_cons_nonint; [exact NonInt_a_lA3|].
  eapply fir_cons_nonint; [exact NonInt_a_lC|].
  eapply fir_cons_int; [exact IsInt_a9|].
  eapply fir_cons_int; [exact IsInt_a1|].
  constructor.
Qed.