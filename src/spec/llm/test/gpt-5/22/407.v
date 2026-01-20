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

Parameters v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom Hv1 : IsInt v1 1%Z.
Axiom Hnv2 : forall n, ~ IsInt v2 n.
Axiom Hnv3 : forall n, ~ IsInt v3 n.
Axiom Hnv4 : forall n, ~ IsInt v4 n.
Axiom Hnv5 : forall n, ~ IsInt v5 n.
Axiom Hv6 : IsInt v6 9%Z.
Axiom Hv7 : IsInt v7 1%Z.

Example test_case_nested: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply Hv1|].
  eapply fir_cons_nonint; [apply Hnv2|].
  eapply fir_cons_nonint; [apply Hnv3|].
  eapply fir_cons_nonint; [apply Hnv4|].
  eapply fir_cons_nonint; [apply Hnv5|].
  eapply fir_cons_int; [apply Hv6|].
  eapply fir_cons_int; [apply Hv7|].
  constructor.
Qed.