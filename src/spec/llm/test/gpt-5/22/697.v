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

Parameters a15 a23 a4 a56 aEmpty1 a7_8 aStr9 aEmpty2 aEmpty3 : Any.
Axiom IsInt_a15 : IsInt a15 15%Z.
Axiom IsInt_a4 : IsInt a4 4%Z.
Axiom nonint_a23 : forall n, ~ IsInt a23 n.
Axiom nonint_a56 : forall n, ~ IsInt a56 n.
Axiom nonint_aEmpty1 : forall n, ~ IsInt aEmpty1 n.
Axiom nonint_a7_8 : forall n, ~ IsInt a7_8 n.
Axiom nonint_aStr9 : forall n, ~ IsInt aStr9 n.
Axiom nonint_aEmpty2 : forall n, ~ IsInt aEmpty2 n.
Axiom nonint_aEmpty3 : forall n, ~ IsInt aEmpty3 n.

Example test_case_new: filter_integers_spec [a15; a23; a4; a56; aEmpty1; a7_8; aStr9; aEmpty2; aEmpty3] [15%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a15|].
  eapply fir_cons_nonint; [apply nonint_a23|].
  eapply fir_cons_int; [apply IsInt_a4|].
  eapply fir_cons_nonint; [apply nonint_a56|].
  eapply fir_cons_nonint; [apply nonint_aEmpty1|].
  eapply fir_cons_nonint; [apply nonint_a7_8|].
  eapply fir_cons_nonint; [apply nonint_aStr9|].
  eapply fir_cons_nonint; [apply nonint_aEmpty2|].
  eapply fir_cons_nonint; [apply nonint_aEmpty3|].
  apply fir_nil.
Qed.