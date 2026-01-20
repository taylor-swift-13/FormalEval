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

Parameter v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Parameter n0 n1 n2 : int.
Axiom A0 : IsInt v0 n0.
Axiom A1 : IsInt v1 n1.
Axiom A3 : IsInt v3 n2.
Axiom A2 : forall n, ~ IsInt v2 n.
Axiom A4 : forall n, ~ IsInt v4 n.
Axiom A5 : forall n, ~ IsInt v5 n.
Axiom A6 : forall n, ~ IsInt v6 n.
Axiom A7 : forall n, ~ IsInt v7 n.
Axiom A8 : forall n, ~ IsInt v8 n.
Axiom A9 : forall n, ~ IsInt v9 n.
Axiom A10 : forall n, ~ IsInt v10 n.

Example test_case_new: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [n0; n1; n2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (n := n0).
  - exact A0.
  - eapply fir_cons_int with (n := n1).
    + exact A1.
    + eapply fir_cons_nonint; [exact A2|].
      eapply fir_cons_int with (n := n2).
      * exact A3.
      * eapply fir_cons_nonint; [exact A4|].
        eapply fir_cons_nonint; [exact A5|].
        eapply fir_cons_nonint; [exact A6|].
        eapply fir_cons_nonint; [exact A7|].
        eapply fir_cons_nonint; [exact A8|].
        eapply fir_cons_nonint; [exact A9|].
        eapply fir_cons_nonint; [exact A10|].
        constructor.
Qed.