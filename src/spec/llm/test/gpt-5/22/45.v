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

Parameter r27 r132 r30 r15a r15b : Any.
Axiom r27_nonint : forall n, ~ IsInt r27 n.
Axiom r132_nonint : forall n, ~ IsInt r132 n.
Axiom r30_nonint : forall n, ~ IsInt r30 n.
Axiom r15a_nonint : forall n, ~ IsInt r15a n.
Axiom r15b_nonint : forall n, ~ IsInt r15b n.

Example test_case_floats: filter_integers_spec [r27; r132; r30; r15a; r15b] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact r27_nonint.
  - eapply fir_cons_nonint.
    + exact r132_nonint.
    + eapply fir_cons_nonint.
      * exact r30_nonint.
      * eapply fir_cons_nonint.
        -- exact r15a_nonint.
        -- eapply fir_cons_nonint.
           ++ exact r15b_nonint.
           ++ constructor.
Qed.