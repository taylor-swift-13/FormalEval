Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
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

Parameter v0 v1 v42 v3 v4 v5 v6 v7 v8 v9 : Any.
Axiom H0 : IsInt v0 0.
Axiom H1 : IsInt v1 1.
Axiom H42 : IsInt v42 42.
Axiom H3 : IsInt v3 3.
Axiom H4 : IsInt v4 4.
Axiom H5 : IsInt v5 5.
Axiom H6 : IsInt v6 6.
Axiom H7 : IsInt v7 7.
Axiom H8 : IsInt v8 8.
Axiom H9 : IsInt v9 9.

Example test_filter_integers : filter_integers_spec [v0; v1; v42; v3; v4; v5; v6; v7; v8; v9] [0; 1; 42; 3; 4; 5; 6; 7; 8; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply H0.
  apply fir_cons_int. apply H1.
  apply fir_cons_int. apply H42.
  apply fir_cons_int. apply H3.
  apply fir_cons_int. apply H4.
  apply fir_cons_int. apply H5.
  apply fir_cons_int. apply H6.
  apply fir_cons_int. apply H7.
  apply fir_cons_int. apply H8.
  apply fir_cons_int. apply H9.
  apply fir_nil.
Qed.