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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Any.
Parameters n10 n9_1 n9_2 n9_3 n9_4 : int.

Axiom IsInt_v1_n10 : IsInt v1 n10.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom IsInt_v6_n9_1 : IsInt v6 n9_1.
Axiom IsInt_v7_n9_2 : IsInt v7 n9_2.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.
Axiom NotInt_v9 : forall n, ~ IsInt v9 n.
Axiom IsInt_v10_n9_3 : IsInt v10 n9_3.
Axiom NotInt_v11 : forall n, ~ IsInt v11 n.
Axiom IsInt_v12_n9_4 : IsInt v12 n9_4.

Example test_case_new:
  filter_integers_spec
    [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12]
    [n10; n9_1; n9_2; n9_3; n9_4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. exact IsInt_v1_n10.
  eapply fir_cons_nonint. exact NotInt_v2.
  eapply fir_cons_nonint. exact NotInt_v3.
  eapply fir_cons_nonint. exact NotInt_v4.
  eapply fir_cons_nonint. exact NotInt_v5.
  eapply fir_cons_int. exact IsInt_v6_n9_1.
  eapply fir_cons_int. exact IsInt_v7_n9_2.
  eapply fir_cons_nonint. exact NotInt_v8.
  eapply fir_cons_nonint. exact NotInt_v9.
  eapply fir_cons_int. exact IsInt_v10_n9_3.
  eapply fir_cons_nonint. exact NotInt_v11.
  eapply fir_cons_int. exact IsInt_v12_n9_4.
  apply fir_nil.
Qed.