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

Parameters v1 v2 v3 v4 v5 v6 : Any.
Axiom IsInt_v1_1 : IsInt v1 1%Z.
Axiom IsInt_v5_7 : IsInt v5 7%Z.
Axiom NonInt_v2 : forall n, ~ IsInt v2 n.
Axiom NonInt_v3 : forall n, ~ IsInt v3 n.
Axiom NonInt_v4 : forall n, ~ IsInt v4 n.
Axiom NonInt_v6 : forall n, ~ IsInt v6 n.

Example test_case_nested: filter_integers_spec [v1; v2; v3; v4; v5; v6] [1%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_v1_1.
  - eapply fir_cons_nonint.
    + exact NonInt_v2.
    + eapply fir_cons_nonint.
      * exact NonInt_v3.
      * eapply fir_cons_nonint.
        -- exact NonInt_v4.
        -- eapply fir_cons_int.
           ++ exact IsInt_v5_7.
           ++ eapply fir_cons_nonint.
              ** exact NonInt_v6.
              ** apply fir_nil.
Qed.