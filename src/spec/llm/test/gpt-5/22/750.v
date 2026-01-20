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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Any.
Parameter i5 iNeg7 i0a i0b : int.
Parameter IsInt_v5 : IsInt v5 i5.
Parameter IsInt_v6 : IsInt v6 iNeg7.
Parameter IsInt_v7 : IsInt v7 i0a.
Parameter IsInt_v14 : IsInt v14 i0b.
Parameter NotInt_v1 : forall n, ~ IsInt v1 n.
Parameter NotInt_v2 : forall n, ~ IsInt v2 n.
Parameter NotInt_v3 : forall n, ~ IsInt v3 n.
Parameter NotInt_v4 : forall n, ~ IsInt v4 n.
Parameter NotInt_v8 : forall n, ~ IsInt v8 n.
Parameter NotInt_v9 : forall n, ~ IsInt v9 n.
Parameter NotInt_v10 : forall n, ~ IsInt v10 n.
Parameter NotInt_v11 : forall n, ~ IsInt v11 n.
Parameter NotInt_v12 : forall n, ~ IsInt v12 n.
Parameter NotInt_v13 : forall n, ~ IsInt v13 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14] [i5; iNeg7; i0a; i0b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NotInt_v1 |].
  eapply fir_cons_nonint; [apply NotInt_v2 |].
  eapply fir_cons_nonint; [apply NotInt_v3 |].
  eapply fir_cons_nonint; [apply NotInt_v4 |].
  eapply fir_cons_int; [apply IsInt_v5 |].
  eapply fir_cons_int; [apply IsInt_v6 |].
  eapply fir_cons_int; [apply IsInt_v7 |].
  eapply fir_cons_nonint; [apply NotInt_v8 |].
  eapply fir_cons_nonint; [apply NotInt_v9 |].
  eapply fir_cons_nonint; [apply NotInt_v10 |].
  eapply fir_cons_nonint; [apply NotInt_v11 |].
  eapply fir_cons_nonint; [apply NotInt_v12 |].
  eapply fir_cons_nonint; [apply NotInt_v13 |].
  eapply fir_cons_int; [apply IsInt_v14 |].
  apply fir_nil.
Qed.