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

Parameter v_int : Any.
Parameter v_three_dict : Any.
Parameter v_list123 : Any.
Parameter v_list45 : Any.
Parameter v_six_dict : Any.

Parameter n_neg85 : int.
Notation "-85%Z" := n_neg85.

Axiom IsInt_v_int : IsInt v_int n_neg85.
Axiom NotInt_v_three_dict : forall n, ~ IsInt v_three_dict n.
Axiom NotInt_v_list123 : forall n, ~ IsInt v_list123 n.
Axiom NotInt_v_list45 : forall n, ~ IsInt v_list45 n.
Axiom NotInt_v_six_dict : forall n, ~ IsInt v_six_dict n.

Example test_case_mixed: filter_integers_spec [v_int; v_three_dict; v_list123; v_list45; v_six_dict] [-85%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact IsInt_v_int.
  - eapply fir_cons_nonint.
    + exact NotInt_v_three_dict.
    + eapply fir_cons_nonint.
      * exact NotInt_v_list123.
      * eapply fir_cons_nonint.
        { exact NotInt_v_list45. }
        { eapply fir_cons_nonint.
          { exact NotInt_v_six_dict. }
          { constructor. } }
Qed.