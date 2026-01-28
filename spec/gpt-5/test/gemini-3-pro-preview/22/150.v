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

Section Test_filter_integers.
  Variable v1 v2 v3 v4 v5 v6 v7 v8 : Any.
  Variable i1 i4 : int.

  Hypothesis H_v1 : IsInt v1 i1.
  Hypothesis H_v2 : forall n, ~ IsInt v2 n.
  Hypothesis H_v3 : IsInt v3 i4.
  Hypothesis H_v4 : forall n, ~ IsInt v4 n.
  Hypothesis H_v5 : forall n, ~ IsInt v5 n.
  Hypothesis H_v6 : forall n, ~ IsInt v6 n.
  Hypothesis H_v7 : forall n, ~ IsInt v7 n.
  Hypothesis H_v8 : forall n, ~ IsInt v8 n.

  Example test_filter_integers_complex : 
    filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [i1; i4].
  Proof.
    unfold filter_integers_spec.
    apply fir_cons_int with (n := i1).
    - exact H_v1.
    - apply fir_cons_nonint.
      + exact H_v2.
      + apply fir_cons_int with (n := i4).
        * exact H_v3.
        * apply fir_cons_nonint.
          -- exact H_v4.
          -- apply fir_cons_nonint.
             ++ exact H_v5.
             ++ apply fir_cons_nonint.
                ** exact H_v6.
                ** apply fir_cons_nonint.
                   --- exact H_v7.
                   --- apply fir_cons_nonint.
                       +++ exact H_v8.
                       +++ apply fir_nil.
  Qed.
End Test_filter_integers.