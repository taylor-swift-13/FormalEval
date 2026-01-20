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
Parameters z1 z9 : int.
Notation "1%Z" := z1.
Notation "9%Z" := z9.
Axiom H_v1_int : IsInt v1 z1.
Axiom H_v6_int : IsInt v6 z9.
Axiom H_v7_int : IsInt v7 z1.
Axiom H_v2_non : forall n, ~ IsInt v2 n.
Axiom H_v3_non : forall n, ~ IsInt v3 n.
Axiom H_v4_non : forall n, ~ IsInt v4 n.
Axiom H_v5_non : forall n, ~ IsInt v5 n.
Axiom H_v8_non : forall n, ~ IsInt v8 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; 9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H_v1_int|].
  eapply fir_cons_nonint; [exact H_v2_non|].
  eapply fir_cons_nonint; [exact H_v3_non|].
  eapply fir_cons_nonint; [exact H_v4_non|].
  eapply fir_cons_nonint; [exact H_v5_non|].
  eapply fir_cons_int; [exact H_v6_int|].
  eapply fir_cons_int; [exact H_v7_int|].
  eapply fir_cons_nonint; [exact H_v8_non|].
  constructor.
Qed.