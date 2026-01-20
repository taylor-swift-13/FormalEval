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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 : Any.
Axiom not_int_a1 : forall n, ~ IsInt a1 n.
Axiom not_int_a2 : forall n, ~ IsInt a2 n.
Axiom isint_a3_8 : IsInt a3 8%Z.
Axiom not_int_a4 : forall n, ~ IsInt a4 n.
Axiom not_int_a5 : forall n, ~ IsInt a5 n.
Axiom not_int_a6 : forall n, ~ IsInt a6 n.
Axiom isint_a7_31 : IsInt a7 31%Z.
Axiom isint_a8_9 : IsInt a8 9%Z.
Axiom not_int_a9 : forall n, ~ IsInt a9 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9] [8%Z; 31%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [ exact not_int_a1 | ].
  eapply fir_cons_nonint; [ exact not_int_a2 | ].
  eapply fir_cons_int with (n := 8%Z); [ exact isint_a3_8 | ].
  eapply fir_cons_nonint; [ exact not_int_a4 | ].
  eapply fir_cons_nonint; [ exact not_int_a5 | ].
  eapply fir_cons_nonint; [ exact not_int_a6 | ].
  eapply fir_cons_int with (n := 31%Z); [ exact isint_a7_31 | ].
  eapply fir_cons_int with (n := 9%Z); [ exact isint_a8_9 | ].
  eapply fir_cons_nonint; [ exact not_int_a9 | ].
  constructor.
Qed.