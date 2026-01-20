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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.
Axiom Hv1 : IsInt v1 1%Z.
Axiom Hv2 : IsInt v2 (-8)%Z.
Axiom Hnv3 : forall n, ~ IsInt v3 n.
Axiom Hv4 : IsInt v4 4%Z.
Axiom Hnv5 : forall n, ~ IsInt v5 n.
Axiom Hnv6 : forall n, ~ IsInt v6 n.
Axiom Hnv7 : forall n, ~ IsInt v7 n.
Axiom Hnv8 : forall n, ~ IsInt v8 n.
Axiom Hnv9 : forall n, ~ IsInt v9 n.
Axiom Hv10 : IsInt v10 31%Z.
Axiom Hv11 : IsInt v11 0%Z.
Axiom Hnv12 : forall n, ~ IsInt v12 n.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12]
    [1%Z; (-8)%Z; 4%Z; 31%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply Hv1|].
  eapply fir_cons_int; [apply Hv2|].
  eapply fir_cons_nonint; [apply Hnv3|].
  eapply fir_cons_int; [apply Hv4|].
  eapply fir_cons_nonint; [apply Hnv5|].
  eapply fir_cons_nonint; [apply Hnv6|].
  eapply fir_cons_nonint; [apply Hnv7|].
  eapply fir_cons_nonint; [apply Hnv8|].
  eapply fir_cons_nonint; [apply Hnv9|].
  eapply fir_cons_int; [apply Hv10|].
  eapply fir_cons_int; [apply Hv11|].
  eapply fir_cons_nonint; [apply Hnv12|].
  constructor.
Qed.