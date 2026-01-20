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

Parameters v1 v2 v3 v4 v5 v6 v7 : Any.
Parameters n1 n2 n3 n4 : int.
Axiom v1_int : IsInt v1 n1.
Axiom v2_int : IsInt v2 n2.
Axiom v3_int : IsInt v3 n3.
Axiom v5_int : IsInt v5 n4.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v6_nonint : forall n, ~ IsInt v6 n.
Axiom v7_nonint : forall n, ~ IsInt v7 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [n1; n2; n3; n4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_int|].
  eapply fir_cons_int; [exact v2_int|].
  eapply fir_cons_int; [exact v3_int|].
  eapply fir_cons_nonint; [exact v4_nonint|].
  eapply fir_cons_int; [exact v5_int|].
  eapply fir_cons_nonint; [exact v6_nonint|].
  eapply fir_cons_nonint; [exact v7_nonint|].
  constructor.
Qed.