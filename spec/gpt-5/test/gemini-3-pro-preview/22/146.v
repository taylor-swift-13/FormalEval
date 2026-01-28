Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter v1_10 : Any.
Parameter v2_nil : Any.
Parameter v3_complex : Any.
Parameter v4_8 : Any.
Parameter v5_l5 : Any.
Parameter v6_l9 : Any.
Parameter v7_9 : Any.
Parameter v8_9 : Any.
Parameter v9_nil : Any.
Parameter v10_l9 : Any.
Parameter v11_9 : Any.
Parameter v12_l9 : Any.

Axiom is_v1 : IsInt v1_10 10%Z.
Axiom not_v2 : forall n, ~ IsInt v2_nil n.
Axiom not_v3 : forall n, ~ IsInt v3_complex n.
Axiom is_v4 : IsInt v4_8 8%Z.
Axiom not_v5 : forall n, ~ IsInt v5_l5 n.
Axiom not_v6 : forall n, ~ IsInt v6_l9 n.
Axiom is_v7 : IsInt v7_9 9%Z.
Axiom is_v8 : IsInt v8_9 9%Z.
Axiom not_v9 : forall n, ~ IsInt v9_nil n.
Axiom not_v10 : forall n, ~ IsInt v10_l9 n.
Axiom is_v11 : IsInt v11_9 9%Z.
Axiom not_v12 : forall n, ~ IsInt v12_l9 n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [v1_10; v2_nil; v3_complex; v4_8; v5_l5; v6_l9; v7_9; v8_9; v9_nil; v10_l9; v11_9; v12_l9]
    [10%Z; 8%Z; 9%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_v1.
  apply fir_cons_nonint. apply not_v2.
  apply fir_cons_nonint. apply not_v3.
  apply fir_cons_int. apply is_v4.
  apply fir_cons_nonint. apply not_v5.
  apply fir_cons_nonint. apply not_v6.
  apply fir_cons_int. apply is_v7.
  apply fir_cons_int. apply is_v8.
  apply fir_cons_nonint. apply not_v9.
  apply fir_cons_nonint. apply not_v10.
  apply fir_cons_int. apply is_v11.
  apply fir_cons_nonint. apply not_v12.
  apply fir_nil.
Qed.