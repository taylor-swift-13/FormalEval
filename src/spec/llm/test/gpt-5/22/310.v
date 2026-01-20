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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom v1_is : IsInt v1 1%Z.
Axiom v2_is : IsInt v2 2%Z.
Axiom v3_non : forall n, ~ IsInt v3 n.
Axiom v4_is : IsInt v4 4%Z.
Axiom v5_non : forall n, ~ IsInt v5 n.
Axiom v6_non : forall n, ~ IsInt v6 n.
Axiom v7_is : IsInt v7 1%Z.
Axiom v8_non : forall n, ~ IsInt v8 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z; 2%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - apply v1_is.
  - apply fir_cons_int with (n := 2%Z).
    + apply v2_is.
    + apply fir_cons_nonint.
      * apply v3_non.
      * apply fir_cons_int with (n := 4%Z).
        -- apply v4_is.
        -- apply fir_cons_nonint.
           ++ apply v5_non.
           ++ apply fir_cons_nonint.
              ** apply v6_non.
              ** apply fir_cons_int with (n := 1%Z).
                 --- apply v7_is.
                 --- apply fir_cons_nonint.
                     +++ apply v8_non.
                     +++ apply fir_nil.
Qed.