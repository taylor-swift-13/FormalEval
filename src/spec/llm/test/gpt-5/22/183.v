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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameters i1 i9 : int.
Axiom v1_is_int1 : IsInt v1 i1.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_is_int9 : IsInt v6 i9.
Axiom v7_is_int1 : IsInt v7 i1.
Axiom v8_is_int1 : IsInt v8 i1.

Example test_case: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [i1; i9; i1; i1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_is_int1|].
  eapply fir_cons_nonint; [apply v2_nonint|].
  eapply fir_cons_nonint; [apply v3_nonint|].
  eapply fir_cons_nonint; [apply v4_nonint|].
  eapply fir_cons_nonint; [apply v5_nonint|].
  eapply fir_cons_int; [apply v6_is_int9|].
  eapply fir_cons_int; [apply v7_is_int1|].
  eapply fir_cons_int; [apply v8_is_int1|].
  constructor.
Qed.