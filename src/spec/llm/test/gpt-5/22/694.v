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

Parameter l1 l2 l3 l4 l5 l6 l7 : Any.
Axiom nonint_l1 : forall n, ~ IsInt l1 n.
Axiom nonint_l2 : forall n, ~ IsInt l2 n.
Axiom nonint_l3 : forall n, ~ IsInt l3 n.
Axiom nonint_l4 : forall n, ~ IsInt l4 n.
Axiom nonint_l5 : forall n, ~ IsInt l5 n.
Axiom nonint_l6 : forall n, ~ IsInt l6 n.
Axiom nonint_l7 : forall n, ~ IsInt l7 n.

Example test_case_nested_lists: filter_integers_spec [l1; l2; l3; l4; l5; l6; l7] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply nonint_l1.
  - eapply fir_cons_nonint.
    + apply nonint_l2.
    + eapply fir_cons_nonint.
      * apply nonint_l3.
      * eapply fir_cons_nonint.
        -- apply nonint_l4.
        -- eapply fir_cons_nonint.
           ++ apply nonint_l5.
           ++ eapply fir_cons_nonint.
              ** apply nonint_l6.
              ** eapply fir_cons_nonint.
                 --- apply nonint_l7.
                 --- constructor.
Qed.