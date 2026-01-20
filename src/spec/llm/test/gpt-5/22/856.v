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

Parameters v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameters i0 i2 i4 : int.
Axiom H_v0_int : IsInt v0 i0.
Axiom H_v1_int : IsInt v1 i2.
Axiom H_v3_int : IsInt v3 i4.
Axiom H_v2_nonint : forall n, ~ IsInt v2 n.
Axiom H_v4_nonint : forall n, ~ IsInt v4 n.
Axiom H_v5_nonint : forall n, ~ IsInt v5 n.
Axiom H_v6_nonint : forall n, ~ IsInt v6 n.
Axiom H_v7_nonint : forall n, ~ IsInt v7 n.
Axiom H_v8_nonint : forall n, ~ IsInt v8 n.
Axiom H_v9_nonint : forall n, ~ IsInt v9 n.

Example test_case_complex: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9] [i0; i2; i4].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := i0).
  - exact H_v0_int.
  - apply fir_cons_int with (n := i2).
    + exact H_v1_int.
    + apply fir_cons_nonint.
      * exact H_v2_nonint.
      * apply fir_cons_int with (n := i4).
        { exact H_v3_int. }
        apply fir_cons_nonint; [exact H_v4_nonint |].
        apply fir_cons_nonint; [exact H_v5_nonint |].
        apply fir_cons_nonint; [exact H_v6_nonint |].
        apply fir_cons_nonint; [exact H_v7_nonint |].
        apply fir_cons_nonint; [exact H_v8_nonint |].
        apply fir_cons_nonint; [exact H_v9_nonint |].
        constructor.
Qed.