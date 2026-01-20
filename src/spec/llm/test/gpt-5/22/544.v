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

Parameter v1 v3 v4 v8 : Any.
Parameter v2 v5 v6 v7 v9 : Any.
Parameter z1 z9 z10 : int.
Notation "1%Z" := z1.
Notation "9%Z" := z9.
Notation "10%Z" := z10.
Parameter Hnv1 : forall n, ~ IsInt v1 n.
Parameter Hnv3 : forall n, ~ IsInt v3 n.
Parameter Hnv4 : forall n, ~ IsInt v4 n.
Parameter Hnv8 : forall n, ~ IsInt v8 n.
Parameter Hi2 : IsInt v2 1%Z.
Parameter Hi5 : IsInt v5 10%Z.
Parameter Hi6 : IsInt v6 9%Z.
Parameter Hi7 : IsInt v7 1%Z.
Parameter Hi9 : IsInt v9 10%Z.

Example test_case_nested:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9]
    [1%Z; 10%Z; 9%Z; 1%Z; 10%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hnv1|].
  eapply (fir_cons_int v2 1%Z); [apply Hi2|].
  eapply fir_cons_nonint; [apply Hnv3|].
  eapply fir_cons_nonint; [apply Hnv4|].
  eapply (fir_cons_int v5 10%Z); [apply Hi5|].
  eapply (fir_cons_int v6 9%Z); [apply Hi6|].
  eapply (fir_cons_int v7 1%Z); [apply Hi7|].
  eapply fir_cons_nonint; [apply Hnv8|].
  eapply (fir_cons_int v9 10%Z); [apply Hi9|].
  constructor.
Qed.