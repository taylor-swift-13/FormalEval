Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter a_empty1 : Any.
Parameter a_empty2 : Any.
Parameter a_list6a : Any.
Parameter a_bools : Any.
Parameter a_list78 : Any.
Parameter a9 : Any.
Parameter a_list6b : Any.

Axiom NonInt_a_empty1 : forall n, ~ IsInt a_empty1 n.
Axiom NonInt_a_empty2 : forall n, ~ IsInt a_empty2 n.
Axiom NonInt_a_list6a : forall n, ~ IsInt a_list6a n.
Axiom NonInt_a_bools : forall n, ~ IsInt a_bools n.
Axiom NonInt_a_list78 : forall n, ~ IsInt a_list78 n.
Axiom NonInt_a_list6b : forall n, ~ IsInt a_list6b n.
Axiom IsInt_a9 : IsInt a9 (9%Z).

Example test_case_new: filter_integers_spec [a_empty1; a_empty2; a_list6a; a_bools; a_list78; a9; a_list6b] [9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_a_empty1|].
  eapply fir_cons_nonint; [apply NonInt_a_empty2|].
  eapply fir_cons_nonint; [apply NonInt_a_list6a|].
  eapply fir_cons_nonint; [apply NonInt_a_bools|].
  eapply fir_cons_nonint; [apply NonInt_a_list78|].
  eapply fir_cons_int; [apply IsInt_a9|].
  eapply fir_cons_nonint; [apply NonInt_a_list6b|].
  constructor.
Qed.