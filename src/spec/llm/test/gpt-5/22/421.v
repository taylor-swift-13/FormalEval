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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameters
  Hv1_nonint : forall n, ~ IsInt v1 n.
Parameters
  Hv2_nonint : forall n, ~ IsInt v2 n.
Parameters
  Hv3_nonint : forall n, ~ IsInt v3 n.
Parameters
  Hv4_nonint : forall n, ~ IsInt v4 n.
Parameters
  Hv5_int : IsInt v5 9%Z.
Parameters
  Hv6_int : IsInt v6 1%Z.
Parameters
  Hv7_nonint : forall n, ~ IsInt v7 n.
Parameters
  Hv8_nonint : forall n, ~ IsInt v8 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hv1_nonint|].
  eapply fir_cons_nonint; [apply Hv2_nonint|].
  eapply fir_cons_nonint; [apply Hv3_nonint|].
  eapply fir_cons_nonint; [apply Hv4_nonint|].
  eapply fir_cons_int; [apply Hv5_int|].
  eapply fir_cons_int; [apply Hv6_int|].
  eapply fir_cons_nonint; [apply Hv7_nonint|].
  eapply fir_cons_nonint; [apply Hv8_nonint|].
  constructor.
Qed.