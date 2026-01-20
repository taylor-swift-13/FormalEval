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

Parameter v_hello v_world v_hhow v_how v_are : Any.
Axiom v_hello_nonint : forall n, ~ IsInt v_hello n.
Axiom v_world_nonint : forall n, ~ IsInt v_world n.
Axiom v_hhow_nonint : forall n, ~ IsInt v_hhow n.
Axiom v_how_nonint : forall n, ~ IsInt v_how n.
Axiom v_are_nonint : forall n, ~ IsInt v_are n.

Example test_case_strings: filter_integers_spec [v_hello; v_world; v_hhow; v_how; v_are] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v_hello_nonint.
  - eapply fir_cons_nonint.
    + exact v_world_nonint.
    + eapply fir_cons_nonint.
      * exact v_hhow_nonint.
      * eapply fir_cons_nonint.
        -- exact v_how_nonint.
        -- eapply fir_cons_nonint.
           ++ exact v_are_nonint.
           ++ constructor.
Qed.