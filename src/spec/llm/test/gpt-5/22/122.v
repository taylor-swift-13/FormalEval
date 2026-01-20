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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.
Parameters i1 i8 i9a i9b : int.
Axiom H1 : IsInt v1 i1.
Axiom H2 : forall n, ~ IsInt v2 n.
Axiom H3 : forall n, ~ IsInt v3 n.
Axiom H4 : IsInt v4 i8.
Axiom H5 : forall n, ~ IsInt v5 n.
Axiom H6 : forall n, ~ IsInt v6 n.
Axiom H7 : IsInt v7 i9a.
Axiom H8 : IsInt v8 i9b.
Axiom H9 : forall n, ~ IsInt v9 n.
Axiom H10 : forall n, ~ IsInt v10 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [i1; i8; i9a; i9b].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 i1 [v2; v3; v4; v5; v6; v7; v8; v9; v10] [i8; i9a; i9b]); [apply H1|].
  apply (fir_cons_nonint v2 [v3; v4; v5; v6; v7; v8; v9; v10] [i8; i9a; i9b]); [apply H2|].
  apply (fir_cons_nonint v3 [v4; v5; v6; v7; v8; v9; v10] [i8; i9a; i9b]); [apply H3|].
  apply (fir_cons_int v4 i8 [v5; v6; v7; v8; v9; v10] [i9a; i9b]); [apply H4|].
  apply (fir_cons_nonint v5 [v6; v7; v8; v9; v10] [i9a; i9b]); [apply H5|].
  apply (fir_cons_nonint v6 [v7; v8; v9; v10] [i9a; i9b]); [apply H6|].
  apply (fir_cons_int v7 i9a [v8; v9; v10] [i9b]); [apply H7|].
  apply (fir_cons_int v8 i9b [v9; v10] []); [apply H8|].
  apply (fir_cons_nonint v9 [v10] []); [apply H9|].
  apply (fir_cons_nonint v10 [] []); [apply H10|].
  apply fir_nil.
Qed.