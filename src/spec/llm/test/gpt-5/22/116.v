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
Parameter one nine : int.
Notation "1%Z" := one.
Notation "9%Z" := nine.

Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_nonint : forall n, ~ IsInt v2 n.
Axiom v3_nonint : forall n, ~ IsInt v3 n.
Axiom v4_nonint : forall n, ~ IsInt v4 n.
Axiom v5_nonint : forall n, ~ IsInt v5 n.
Axiom v6_is_int : IsInt v6 9%Z.
Axiom v7_is_int : IsInt v7 9%Z.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [1%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 1%Z [v2; v3; v4; v5; v6; v7] [9%Z; 9%Z]).
  - exact v1_is_int.
  - apply (fir_cons_nonint v2 [v3; v4; v5; v6; v7] [9%Z; 9%Z]).
    + exact v2_nonint.
    + apply (fir_cons_nonint v3 [v4; v5; v6; v7] [9%Z; 9%Z]).
      * exact v3_nonint.
      * apply (fir_cons_nonint v4 [v5; v6; v7] [9%Z; 9%Z]).
        -- exact v4_nonint.
        -- apply (fir_cons_nonint v5 [v6; v7] [9%Z; 9%Z]).
           ++ exact v5_nonint.
           ++ apply (fir_cons_int v6 9%Z [v7] [9%Z]).
              ** exact v6_is_int.
              ** apply (fir_cons_int v7 9%Z [] []).
                 --- exact v7_is_int.
                 --- apply fir_nil.
Qed.