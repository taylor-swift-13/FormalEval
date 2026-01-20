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

Parameter v0 v1 v2 v3 v4 v5 v6 v7 : Any.
Parameter n0 n4 n61 : int.
Parameter H0 : IsInt v0 n0.
Parameter H1 : forall n, ~ IsInt v1 n.
Parameter H2 : IsInt v2 n4.
Parameter H3 : forall n, ~ IsInt v3 n.
Parameter H4 : IsInt v4 n61.
Parameter H5 : forall n, ~ IsInt v5 n.
Parameter H6 : forall n, ~ IsInt v6 n.
Parameter H7 : forall n, ~ IsInt v7 n.

Example test_case_new: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7] [n0; n4; n61].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H0|].
  eapply fir_cons_nonint; [exact H1|].
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_nonint; [exact H3|].
  eapply fir_cons_int; [exact H4|].
  eapply fir_cons_nonint; [exact H5|].
  eapply fir_cons_nonint; [exact H6|].
  eapply fir_cons_nonint; [exact H7|].
  constructor.
Qed.