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

Parameter v_2_5R : Any.
Parameter v_3_2332014890113814R : Any.
Parameter v_4_6R : Any.
Parameter v_7_8R : Any.
Parameter v_abc : Any.
Parameter v_empty_obj : Any.

Axiom v_2_5R_nonint : forall n, ~ IsInt v_2_5R n.
Axiom v_3_2332014890113814R_nonint : forall n, ~ IsInt v_3_2332014890113814R n.
Axiom v_4_6R_nonint : forall n, ~ IsInt v_4_6R n.
Axiom v_7_8R_nonint : forall n, ~ IsInt v_7_8R n.
Axiom v_abc_nonint : forall n, ~ IsInt v_abc n.
Axiom v_empty_obj_nonint : forall n, ~ IsInt v_empty_obj n.

Example test_case_mixed_nonints:
  filter_integers_spec [v_2_5R; v_3_2332014890113814R; v_4_6R; v_7_8R; v_abc; v_empty_obj] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v_2_5R_nonint.
  - eapply fir_cons_nonint.
    + exact v_3_2332014890113814R_nonint.
    + eapply fir_cons_nonint.
      * exact v_4_6R_nonint.
      * eapply fir_cons_nonint.
        { exact v_7_8R_nonint. }
        { eapply fir_cons_nonint.
          - exact v_abc_nonint.
          - eapply fir_cons_nonint.
            + exact v_empty_obj_nonint.
            + constructor. }
Qed.