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

Parameter v1 v2 v3 v4 v5 v6 v7 : Any.
Parameter i1 i7 : int.

Axiom v1_is_int : IsInt v1 i1.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_is_int : IsInt v6 i7.
Axiom v7_not_int : forall n, ~ IsInt v7 n.

Example test_filter_integers_mixed : filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [i1; i7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int.
  - apply v1_is_int.
  - apply fir_cons_nonint.
    + apply v2_not_int.
    + apply fir_cons_nonint.
      * apply v3_not_int.
      * apply fir_cons_nonint.
        -- apply v4_not_int.
        -- apply fir_cons_nonint.
           ++ apply v5_not_int.
           ++ apply fir_cons_int.
              ** apply v6_is_int.
              ** apply fir_cons_nonint.
                 --- apply v7_not_int.
                 --- apply fir_nil.
Qed.