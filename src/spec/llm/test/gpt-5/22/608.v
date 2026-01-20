Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Definition int := Z.
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

Parameter a1 a23 a94a a94b a56 a78 a9 : Any.
Axiom IsInt_a1 : IsInt a1 1%Z.
Axiom NonInt_a23 : forall n, ~ IsInt a23 n.
Axiom NonInt_a94a : forall n, ~ IsInt a94a n.
Axiom NonInt_a94b : forall n, ~ IsInt a94b n.
Axiom NonInt_a56 : forall n, ~ IsInt a56 n.
Axiom NonInt_a78 : forall n, ~ IsInt a78 n.
Axiom IsInt_a9 : IsInt a9 9%Z.

Example test_case_nested: filter_integers_spec [a1; a23; a94a; a94b; a56; a78; a9] [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_nonint; [apply NonInt_a23|].
  eapply fir_cons_nonint; [apply NonInt_a94a|].
  eapply fir_cons_nonint; [apply NonInt_a94b|].
  eapply fir_cons_nonint; [apply NonInt_a56|].
  eapply fir_cons_nonint; [apply NonInt_a78|].
  eapply fir_cons_int; [apply IsInt_a9|].
  constructor.
Qed.