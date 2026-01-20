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

Parameter v1 v2 v3 v4 : Any.
Parameter v1_nonint : forall n, ~ IsInt v1 n.
Parameter v2_nonint : forall n, ~ IsInt v2 n.
Parameter v3_nonint : forall n, ~ IsInt v3 n.
Parameter v4_nonint : forall n, ~ IsInt v4 n.

Example test_case_floats: filter_integers_spec [v1; v2; v3; v4] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v1_nonint.
  - eapply fir_cons_nonint.
    + exact v2_nonint.
    + eapply fir_cons_nonint.
      * exact v3_nonint.
      * eapply fir_cons_nonint.
        -- exact v4_nonint.
        -- constructor.
Qed.