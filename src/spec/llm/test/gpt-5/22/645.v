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

Parameter v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameter n0 n1 n2 : int.

Axiom IsInt_v0 : IsInt v0 n0.
Axiom IsInt_v1 : IsInt v1 n1.
Axiom IsInt_v3 : IsInt v3 n2.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom NotInt_v6 : forall n, ~ IsInt v6 n.
Axiom NotInt_v7 : forall n, ~ IsInt v7 n.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.
Axiom NotInt_v9 : forall n, ~ IsInt v9 n.

Example test_case_new:
  filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9] [n0; n1; n2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v0|].
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_nonint; [exact NotInt_v2|].
  eapply fir_cons_int; [exact IsInt_v3|].
  eapply fir_cons_nonint; [exact NotInt_v4|].
  eapply fir_cons_nonint; [exact NotInt_v5|].
  eapply fir_cons_nonint; [exact NotInt_v6|].
  eapply fir_cons_nonint; [exact NotInt_v7|].
  eapply fir_cons_nonint; [exact NotInt_v8|].
  eapply fir_cons_nonint; [exact NotInt_v9|].
  constructor.
Qed.