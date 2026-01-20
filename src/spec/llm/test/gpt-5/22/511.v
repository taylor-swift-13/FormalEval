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

Parameter z1 : int.
Notation "1%Z" := z1.

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom V1_is_int : IsInt v1 1%Z.
Axiom V2_nonint : forall n, ~ IsInt v2 n.
Axiom V3_nonint : forall n, ~ IsInt v3 n.
Axiom V4_nonint : forall n, ~ IsInt v4 n.
Axiom V5_nonint : forall n, ~ IsInt v5 n.
Axiom V6_nonint : forall n, ~ IsInt v6 n.
Axiom V7_nonint : forall n, ~ IsInt v7 n.
Axiom V8_is_int : IsInt v8 1%Z.

Example test_case_mixed_nested: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply V1_is_int|].
  eapply fir_cons_nonint; [apply V2_nonint|].
  eapply fir_cons_nonint; [apply V3_nonint|].
  eapply fir_cons_nonint; [apply V4_nonint|].
  eapply fir_cons_nonint; [apply V5_nonint|].
  eapply fir_cons_nonint; [apply V6_nonint|].
  eapply fir_cons_nonint; [apply V7_nonint|].
  eapply fir_cons_int; [apply V8_is_int|].
  constructor.
Qed.