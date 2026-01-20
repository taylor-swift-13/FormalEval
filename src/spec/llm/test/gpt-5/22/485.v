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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameter i1 i9 : int.
Notation "1%Z" := i1.
Notation "9%Z" := i9.
Axiom v1_nonint : forall n, ~ IsInt v1 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.
Axiom v8_nonint : forall n, ~ IsInt v8 n.
Axiom v9_nonint : forall n, ~ IsInt v9 n.
Axiom v2_is_1 : IsInt v2 i1.
Axiom v6_is_9 : IsInt v6 i9.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v1_nonint|].
  eapply fir_cons_int; [apply v2_is_1|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_nonint; [apply v4_nonint|].
  eapply fir_cons_nonint; [apply v5_nonint|].
  eapply fir_cons_int; [apply v6_is_9|].
  eapply fir_cons_nonint; [apply v7_nonint|].
  eapply fir_cons_nonint; [apply v8_nonint|].
  eapply fir_cons_nonint; [apply v9_nonint|].
  constructor.
Qed.