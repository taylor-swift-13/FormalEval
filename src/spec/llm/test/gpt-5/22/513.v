Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Axiom H_v1 : forall n, ~ IsInt v1 n.
Axiom H_v2 : IsInt v2 4%Z.
Axiom H_v3 : forall n, ~ IsInt v3 n.
Axiom H_v4 : forall n, ~ IsInt v4 n.
Axiom H_v5 : forall n, ~ IsInt v5 n.
Axiom H_v6 : forall n, ~ IsInt v6 n.
Axiom H_v7 : IsInt v7 8%Z.
Axiom H_v8 : IsInt v8 4%Z.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [4%Z; 8%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact H_v1.
  - eapply fir_cons_int.
    + exact H_v2.
    + eapply fir_cons_nonint.
      * exact H_v3.
      * eapply fir_cons_nonint.
        -- exact H_v4.
        -- eapply fir_cons_nonint.
           ++ exact H_v5.
           ++ eapply fir_cons_nonint.
              ** exact H_v6.
              ** eapply fir_cons_int.
                 --- exact H_v7.
                 --- eapply fir_cons_int.
                     +++ exact H_v8.
                     +++ apply fir_nil.
Qed.