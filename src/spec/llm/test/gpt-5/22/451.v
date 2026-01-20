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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Any.
Parameters z5 z0 : int.
Axiom HN1 : forall n, ~ IsInt v1 n.
Axiom HN2 : forall n, ~ IsInt v2 n.
Axiom HN3 : forall n, ~ IsInt v3 n.
Axiom HN4 : forall n, ~ IsInt v4 n.
Axiom HI5 : IsInt v5 z5.
Axiom HN6 : forall n, ~ IsInt v6 n.
Axiom HI7 : IsInt v7 z0.
Axiom HN8 : forall n, ~ IsInt v8 n.
Axiom HN9 : forall n, ~ IsInt v9 n.
Axiom HN10 : forall n, ~ IsInt v10 n.
Axiom HN11 : forall n, ~ IsInt v11 n.
Axiom HN12 : forall n, ~ IsInt v12 n.
Axiom HN13 : forall n, ~ IsInt v13 n.
Axiom HN14 : forall n, ~ IsInt v14 n.
Axiom HN15 : forall n, ~ IsInt v15 n.
Axiom HI16 : IsInt v16 z5.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16] [z5; z0; z5].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply HN1 |].
  eapply fir_cons_nonint; [apply HN2 |].
  eapply fir_cons_nonint; [apply HN3 |].
  eapply fir_cons_nonint; [apply HN4 |].
  eapply fir_cons_int; [apply HI5 |].
  eapply fir_cons_nonint; [apply HN6 |].
  eapply fir_cons_int; [apply HI7 |].
  eapply fir_cons_nonint; [apply HN8 |].
  eapply fir_cons_nonint; [apply HN9 |].
  eapply fir_cons_nonint; [apply HN10 |].
  eapply fir_cons_nonint; [apply HN11 |].
  eapply fir_cons_nonint; [apply HN12 |].
  eapply fir_cons_nonint; [apply HN13 |].
  eapply fir_cons_nonint; [apply HN14 |].
  eapply fir_cons_nonint; [apply HN15 |].
  eapply fir_cons_int; [apply HI16 |].
  apply fir_nil.
Qed.