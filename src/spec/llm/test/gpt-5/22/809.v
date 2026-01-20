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

Parameter v2 v3 v_four v_float1 v5 v_seven v_str8 v_float2 v_float3 v_four2 : Any.
Parameter n2 n3 n5 : int.
Axiom H2 : IsInt v2 n2.
Axiom H3 : IsInt v3 n3.
Axiom H5 : IsInt v5 n5.
Axiom not_int_v_four : forall n, ~ IsInt v_four n.
Axiom not_int_v_float1 : forall n, ~ IsInt v_float1 n.
Axiom not_int_v_seven : forall n, ~ IsInt v_seven n.
Axiom not_int_v_str8 : forall n, ~ IsInt v_str8 n.
Axiom not_int_v_float2 : forall n, ~ IsInt v_float2 n.
Axiom not_int_v_float3 : forall n, ~ IsInt v_float3 n.
Axiom not_int_v_four2 : forall n, ~ IsInt v_four2 n.

Example test_case_mixed:
  filter_integers_spec
    [v2; v3; v_four; v_float1; v5; v_seven; v_str8; v_float2; v_float3; v_four2]
    [n2; n3; n5].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply not_int_v_four|].
  eapply fir_cons_nonint; [apply not_int_v_float1|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply not_int_v_seven|].
  eapply fir_cons_nonint; [apply not_int_v_str8|].
  eapply fir_cons_nonint; [apply not_int_v_float2|].
  eapply fir_cons_nonint; [apply not_int_v_float3|].
  eapply fir_cons_nonint; [apply not_int_v_four2|].
  constructor.
Qed.