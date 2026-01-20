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

Parameter v2_5R : Any.
Parameter v4_6R : Any.
Parameter v7_8R : Any.
Parameter v_abc : Any.
Parameter v_empty_record : Any.
Parameter v_abchaFbcowF : Any.
Parameter v_empty_list : Any.

Axiom v2_5R_nonint : forall n, ~ IsInt v2_5R n.
Axiom v4_6R_nonint : forall n, ~ IsInt v4_6R n.
Axiom v7_8R_nonint : forall n, ~ IsInt v7_8R n.
Axiom v_abc_nonint : forall n, ~ IsInt v_abc n.
Axiom v_empty_record_nonint : forall n, ~ IsInt v_empty_record n.
Axiom v_abchaFbcowF_nonint : forall n, ~ IsInt v_abchaFbcowF n.
Axiom v_empty_list_nonint : forall n, ~ IsInt v_empty_list n.

Example test_case_nonints: filter_integers_spec [v2_5R; v4_6R; v7_8R; v_abc; v_empty_record; v_abchaFbcowF; v_empty_list] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply v2_5R_nonint.
  - eapply fir_cons_nonint.
    + apply v4_6R_nonint.
    + eapply fir_cons_nonint.
      * apply v7_8R_nonint.
      * eapply fir_cons_nonint.
        { apply v_abc_nonint. }
        { eapply fir_cons_nonint.
          - apply v_empty_record_nonint.
          - eapply fir_cons_nonint.
            + apply v_abchaFbcowF_nonint.
            + eapply fir_cons_nonint.
              * apply v_empty_list_nonint.
              * constructor. }
Qed.