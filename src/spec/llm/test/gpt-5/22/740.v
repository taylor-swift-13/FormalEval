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

Parameter v_two_str2 v_three_list3_four v_seven_str7 v_empty_dict v_five5_six_str6 : Any.
Axiom NotInt_v_two_str2 : forall n, ~ IsInt v_two_str2 n.
Axiom NotInt_v_three_list3_four : forall n, ~ IsInt v_three_list3_four n.
Axiom NotInt_v_seven_str7 : forall n, ~ IsInt v_seven_str7 n.
Axiom NotInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NotInt_v_five5_six_str6 : forall n, ~ IsInt v_five5_six_str6 n.

Example test_case_new:
  filter_integers_spec
    [v_two_str2; v_three_list3_four; v_seven_str7; v_empty_dict; v_five5_six_str6; v_empty_dict; v_seven_str7]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact NotInt_v_two_str2.
  - eapply fir_cons_nonint.
    + exact NotInt_v_three_list3_four.
    + eapply fir_cons_nonint.
      * exact NotInt_v_seven_str7.
      * eapply fir_cons_nonint.
        { exact NotInt_v_empty_dict. }
        { eapply fir_cons_nonint.
          - exact NotInt_v_five5_six_str6.
          - eapply fir_cons_nonint.
            + exact NotInt_v_empty_dict.
            + eapply fir_cons_nonint.
              * exact NotInt_v_seven_str7.
              * constructor. }
Qed.