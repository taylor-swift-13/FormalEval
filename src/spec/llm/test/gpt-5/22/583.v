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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v3 : IsInt v3 4%Z.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom IsInt_v6 : IsInt v6 7%Z.
Axiom NotInt_v7 : forall n, ~ IsInt v7 n.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; 2%Z; 4%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (v := v1) (n := 1%Z).
  - apply IsInt_v1.
  - apply fir_cons_int with (v := v2) (n := 2%Z).
    + apply IsInt_v2.
    + apply fir_cons_int with (v := v3) (n := 4%Z).
      * apply IsInt_v3.
      * apply fir_cons_nonint with (v := v4).
        -- apply NotInt_v4.
        -- apply fir_cons_nonint with (v := v5).
           ++ apply NotInt_v5.
           ++ apply fir_cons_int with (v := v6) (n := 7%Z).
              ** apply IsInt_v6.
              ** apply fir_cons_nonint with (v := v7).
                 --- apply NotInt_v7.
                 --- apply fir_cons_nonint with (v := v8).
                     **** apply NotInt_v8.
                     **** apply fir_nil.
Qed.