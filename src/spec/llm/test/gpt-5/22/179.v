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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameter z1 z2 z4 : int.

Axiom H1 : IsInt v1 z1.
Axiom H2 : IsInt v2 z2.
Axiom H3 : forall n, ~ IsInt v3 n.
Axiom H4 : IsInt v4 z4.
Axiom H5 : forall n, ~ IsInt v5 n.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : forall n, ~ IsInt v7 n.
Axiom H8 : IsInt v8 z1.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [z1; z2; z4; z1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_int; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_nonint; [apply H7|].
  eapply fir_cons_int; [apply H8|].
  constructor.
Qed.