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

Parameter l1 l2 l3 l4 : Any.
Axiom l1_nonint : forall n, ~ IsInt l1 n.
Axiom l2_nonint : forall n, ~ IsInt l2 n.
Axiom l3_nonint : forall n, ~ IsInt l3 n.
Axiom l4_nonint : forall n, ~ IsInt l4 n.

Example test_case_nested_lists: filter_integers_spec [l1; l2; l3; l4] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply l1_nonint.
  - eapply fir_cons_nonint.
    + apply l2_nonint.
    + eapply fir_cons_nonint.
      * apply l3_nonint.
      * eapply fir_cons_nonint.
        { apply l4_nonint. }
        { constructor. }
Qed.