Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter v_false v_none v_r1_3 v_5 v_neg7 v_0 v_r1_050449309718769 v_a v_b v_empty v_dict v_list34 v_list56_6_7 : Any.

Axiom IsInt_v_5 : IsInt v_5 5%Z.
Axiom IsInt_v_neg7 : IsInt v_neg7 (-7)%Z.
Axiom IsInt_v_0 : IsInt v_0 0%Z.

Axiom not_int_false : forall n, ~ IsInt v_false n.
Axiom not_int_none : forall n, ~ IsInt v_none n.
Axiom not_int_r1_3 : forall n, ~ IsInt v_r1_3 n.
Axiom not_int_r1_050449309718769 : forall n, ~ IsInt v_r1_050449309718769 n.
Axiom not_int_a : forall n, ~ IsInt v_a n.
Axiom not_int_b : forall n, ~ IsInt v_b n.
Axiom not_int_empty : forall n, ~ IsInt v_empty n.
Axiom not_int_dict : forall n, ~ IsInt v_dict n.
Axiom not_int_list34 : forall n, ~ IsInt v_list34 n.
Axiom not_int_list56_6_7 : forall n, ~ IsInt v_list56_6_7 n.

Example test_case_mixed:
  filter_integers_spec
    [v_false; v_none; v_r1_3; v_5; v_neg7; v_0; v_r1_050449309718769; v_a; v_b; v_empty; v_dict; v_list34; v_list56_6_7]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact not_int_false.
  eapply fir_cons_nonint. exact not_int_none.
  eapply fir_cons_nonint. exact not_int_r1_3.
  eapply fir_cons_int. exact IsInt_v_5.
  eapply fir_cons_int. exact IsInt_v_neg7.
  eapply fir_cons_int. exact IsInt_v_0.
  eapply fir_cons_nonint. exact not_int_r1_050449309718769.
  eapply fir_cons_nonint. exact not_int_a.
  eapply fir_cons_nonint. exact not_int_b.
  eapply fir_cons_nonint. exact not_int_empty.
  eapply fir_cons_nonint. exact not_int_dict.
  eapply fir_cons_nonint. exact not_int_list34.
  eapply fir_cons_nonint. exact not_int_list56_6_7.
  constructor.
Qed.