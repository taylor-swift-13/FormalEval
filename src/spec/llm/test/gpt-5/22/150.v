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

Parameter a1 a23 a4 a5 a_empty a7_8 a_obj a_str9 : Any.
Axiom IsInt_a1 : IsInt a1 1%Z.
Axiom IsInt_a4 : IsInt a4 4%Z.
Axiom not_int_a23 : forall n, ~ IsInt a23 n.
Axiom not_int_a5 : forall n, ~ IsInt a5 n.
Axiom not_int_a_empty : forall n, ~ IsInt a_empty n.
Axiom not_int_a7_8 : forall n, ~ IsInt a7_8 n.
Axiom not_int_a_obj : forall n, ~ IsInt a_obj n.
Axiom not_int_a_str9 : forall n, ~ IsInt a_str9 n.

Example test_case_mixed: filter_integers_spec [a1; a23; a4; a5; a_empty; a7_8; a_obj; a_str9] [1%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_nonint; [apply not_int_a23|].
  eapply fir_cons_int; [apply IsInt_a4|].
  eapply fir_cons_nonint; [apply not_int_a5|].
  eapply fir_cons_nonint; [apply not_int_a_empty|].
  eapply fir_cons_nonint; [apply not_int_a7_8|].
  eapply fir_cons_nonint; [apply not_int_a_obj|].
  eapply fir_cons_nonint; [apply not_int_a_str9|].
  constructor.
Qed.