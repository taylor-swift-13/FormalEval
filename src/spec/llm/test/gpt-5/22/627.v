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

Parameters b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Any.
Axiom nonint_b1 : forall n, ~ IsInt b1 n.
Axiom nonint_b2 : forall n, ~ IsInt b2 n.
Axiom nonint_b3 : forall n, ~ IsInt b3 n.
Axiom nonint_b4 : forall n, ~ IsInt b4 n.
Axiom nonint_b5 : forall n, ~ IsInt b5 n.
Axiom nonint_b6 : forall n, ~ IsInt b6 n.
Axiom nonint_b7 : forall n, ~ IsInt b7 n.
Axiom nonint_b8 : forall n, ~ IsInt b8 n.
Axiom nonint_b9 : forall n, ~ IsInt b9 n.
Axiom nonint_b10 : forall n, ~ IsInt b10 n.

Example test_case_booleans: filter_integers_spec [b1; b2; b3; b4; b5; b6; b7; b8; b9; b10] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_b1 |].
  eapply fir_cons_nonint; [apply nonint_b2 |].
  eapply fir_cons_nonint; [apply nonint_b3 |].
  eapply fir_cons_nonint; [apply nonint_b4 |].
  eapply fir_cons_nonint; [apply nonint_b5 |].
  eapply fir_cons_nonint; [apply nonint_b6 |].
  eapply fir_cons_nonint; [apply nonint_b7 |].
  eapply fir_cons_nonint; [apply nonint_b8 |].
  eapply fir_cons_nonint; [apply nonint_b9 |].
  eapply fir_cons_nonint; [apply nonint_b10 |].
  constructor.
Qed.