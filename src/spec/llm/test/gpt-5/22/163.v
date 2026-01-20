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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameter n0 n1 : int.
Axiom not_int_v1 : forall n, ~ IsInt v1 n.
Axiom is_int_v2 : IsInt v2 n0.
Axiom not_int_v3 : forall n, ~ IsInt v3 n.
Axiom not_int_v4 : forall n, ~ IsInt v4 n.
Axiom not_int_v5 : forall n, ~ IsInt v5 n.
Axiom not_int_v6 : forall n, ~ IsInt v6 n.
Axiom not_int_v7 : forall n, ~ IsInt v7 n.
Axiom is_int_v8 : IsInt v8 n1.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [n0; n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply not_int_v1 |].
  eapply fir_cons_int; [apply is_int_v2 |].
  eapply fir_cons_nonint; [apply not_int_v3 |].
  eapply fir_cons_nonint; [apply not_int_v4 |].
  eapply fir_cons_nonint; [apply not_int_v5 |].
  eapply fir_cons_nonint; [apply not_int_v6 |].
  eapply fir_cons_nonint; [apply not_int_v7 |].
  eapply fir_cons_int; [apply is_int_v8 |].
  apply fir_nil.
Qed.