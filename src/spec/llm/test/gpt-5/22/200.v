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

Parameters v1_1Z v2_2Z v3_3Z v4_str8 v5_5p5R v6_6Z v7_seven v8_str8 v9_9p0R : Any.
Parameters n1_1Z n2_2Z n3_3Z n6_6Z : int.

Axiom v1_1Z_isint : IsInt v1_1Z n1_1Z.
Axiom v2_2Z_isint : IsInt v2_2Z n2_2Z.
Axiom v3_3Z_isint : IsInt v3_3Z n3_3Z.
Axiom v4_str8_notint : forall n, ~ IsInt v4_str8 n.
Axiom v5_5p5R_notint : forall n, ~ IsInt v5_5p5R n.
Axiom v6_6Z_isint : IsInt v6_6Z n6_6Z.
Axiom v7_seven_notint : forall n, ~ IsInt v7_seven n.
Axiom v8_str8_notint : forall n, ~ IsInt v8_str8 n.
Axiom v9_9p0R_notint : forall n, ~ IsInt v9_9p0R n.

Example test_case_mixed:
  filter_integers_spec
    [v1_1Z; v2_2Z; v3_3Z; v4_str8; v5_5p5R; v6_6Z; v7_seven; v8_str8; v9_9p0R]
    [n1_1Z; n2_2Z; n3_3Z; n6_6Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_1Z_isint|].
  eapply fir_cons_int; [apply v2_2Z_isint|].
  eapply fir_cons_int; [apply v3_3Z_isint|].
  eapply fir_cons_nonint; [apply v4_str8_notint|].
  eapply fir_cons_nonint; [apply v5_5p5R_notint|].
  eapply fir_cons_int; [apply v6_6Z_isint|].
  eapply fir_cons_nonint; [apply v7_seven_notint|].
  eapply fir_cons_nonint; [apply v8_str8_notint|].
  eapply fir_cons_nonint; [apply v9_9p0R_notint|].
  constructor.
Qed.