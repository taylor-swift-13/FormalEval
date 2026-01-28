Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom Ax_v1 : IsInt v1 1%Z.
Axiom Ax_v2 : forall n, ~ IsInt v2 n.
Axiom Ax_v3 : forall n, ~ IsInt v3 n.
Axiom Ax_v4 : forall n, ~ IsInt v4 n.
Axiom Ax_v5 : forall n, ~ IsInt v5 n.
Axiom Ax_v6 : IsInt v6 9%Z.
Axiom Ax_v7 : forall n, ~ IsInt v7 n.

Example test_filter_integers : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - apply Ax_v1.
  - apply fir_cons_nonint.
    + apply Ax_v2.
    + apply fir_cons_nonint.
      * apply Ax_v3.
      * apply fir_cons_nonint.
        -- apply Ax_v4.
        -- apply fir_cons_nonint.
           ++ apply Ax_v5.
           ++ apply fir_cons_int with (n := 9%Z).
              ** apply Ax_v6.
              ** apply fir_cons_nonint.
                 --- apply Ax_v7.
                 --- apply fir_nil.
Qed.