Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.
Parameter Any : Type.
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
Axiom v1_is_1 : IsInt v1 1.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_is_9 : IsInt v6 9.
Axiom v7_is_1 : IsInt v7 1.

Example test_filter_integers_complex : 
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1; 9; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply v1_is_1.
  - apply fir_cons_nonint.
    + apply v2_not_int.
    + apply fir_cons_nonint.
      * apply v3_not_int.
      * apply fir_cons_nonint.
        -- apply v4_not_int.
        -- apply fir_cons_nonint.
           ++ apply v5_not_int.
           ++ apply fir_cons_int with (n := 9).
              ** apply v6_is_9.
              ** apply fir_cons_int with (n := 1).
                 --- apply v7_is_1.
                 --- apply fir_nil.
Qed.