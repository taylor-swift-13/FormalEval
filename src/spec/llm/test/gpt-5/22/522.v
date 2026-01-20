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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Any.
Parameter n1 n4 n1' n4' n4'' n4''' n4'''' n4''''' : int.

Hypothesis H1 : IsInt v1 n1.
Hypothesis H2 : forall n, ~ IsInt v2 n.
Hypothesis H3 : IsInt v3 n4.
Hypothesis H4 : forall n, ~ IsInt v4 n.
Hypothesis H5 : forall n, ~ IsInt v5 n.
Hypothesis H6 : forall n, ~ IsInt v6 n.
Hypothesis H7 : IsInt v7 n1'.
Hypothesis H8 : IsInt v8 n4'.
Hypothesis H9 : IsInt v9 n4''.
Hypothesis H10 : IsInt v10 n4'''.
Hypothesis H11 : IsInt v11 n4''''.
Hypothesis H12 : IsInt v12 n4'''''.
Hypothesis H13 : forall n, ~ IsInt v13 n.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13]
    [n1; n4; n1'; n4'; n4''; n4'''; n4''''; n4'''''].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_nonint; [exact H2|].
  eapply fir_cons_int; [exact H3|].
  eapply fir_cons_nonint; [exact H4|].
  eapply fir_cons_nonint; [exact H5|].
  eapply fir_cons_nonint; [exact H6|].
  eapply fir_cons_int; [exact H7|].
  eapply fir_cons_int; [exact H8|].
  eapply fir_cons_int; [exact H9|].
  eapply fir_cons_int; [exact H10|].
  eapply fir_cons_int; [exact H11|].
  eapply fir_cons_int; [exact H12|].
  eapply fir_cons_nonint; [exact H13|].
  constructor.
Qed.