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
Parameter n1 : int.
Axiom H_v1_int : IsInt v1 n1.
Axiom H_v2_non : forall n, ~ IsInt v2 n.
Axiom H_v3_non : forall n, ~ IsInt v3 n.
Axiom H_v4_non : forall n, ~ IsInt v4 n.
Axiom H_v5_non : forall n, ~ IsInt v5 n.
Axiom H_v6_non : forall n, ~ IsInt v6 n.
Axiom H_v7_non : forall n, ~ IsInt v7 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7] [n1].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 n1 [v2; v3; v4; v5; v6; v7] []).
  - exact H_v1_int.
  - apply (fir_cons_nonint v2 [v3; v4; v5; v6; v7] []).
    + exact H_v2_non.
    + apply (fir_cons_nonint v3 [v4; v5; v6; v7] []).
      * exact H_v3_non.
      * apply (fir_cons_nonint v4 [v5; v6; v7] []).
        -- exact H_v4_non.
        -- apply (fir_cons_nonint v5 [v6; v7] []).
           ++ exact H_v5_non.
           ++ apply (fir_cons_nonint v6 [v7] []).
              ** exact H_v6_non.
              ** apply (fir_cons_nonint v7 [] []).
                 --- exact H_v7_non.
                 --- constructor.
Qed.