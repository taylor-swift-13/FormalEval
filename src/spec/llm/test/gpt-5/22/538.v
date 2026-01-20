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

Parameter a1 a2 a3 a4 a5 a6 a7 : Any.
Parameter i1 i2 i4 : int.

Axiom IsInt_a1 : IsInt a1 i1.
Axiom IsInt_a2 : IsInt a2 i2.
Axiom IsInt_a4 : IsInt a4 i4.

Axiom NonInt_a3 : forall n, ~ IsInt a3 n.
Axiom NonInt_a5 : forall n, ~ IsInt a5 n.
Axiom NonInt_a6 : forall n, ~ IsInt a6 n.
Axiom NonInt_a7 : forall n, ~ IsInt a7 n.

Notation "1%Z" := i1.
Notation "2%Z" := i2.
Notation "4%Z" := i4.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a1] [1%Z; 2%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [ apply IsInt_a1 | ].
  eapply fir_cons_int; [ apply IsInt_a2 | ].
  eapply fir_cons_nonint; [ apply NonInt_a3 | ].
  eapply fir_cons_int; [ apply IsInt_a4 | ].
  eapply fir_cons_nonint; [ apply NonInt_a5 | ].
  eapply fir_cons_nonint; [ apply NonInt_a6 | ].
  eapply fir_cons_nonint; [ apply NonInt_a7 | ].
  eapply fir_cons_int; [ apply IsInt_a1 | ].
  constructor.
Qed.