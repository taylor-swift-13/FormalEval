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

Parameter v_true v_false v_None v_real_1_3
          v_5 v_neg7 v_0
          v_a v_b v_empty_list v_empty_dict v_dict_a1 v_list_34 v_list_56_7 : Any.

Axiom v_true_not_int : forall n, ~ IsInt v_true n.
Axiom v_false_not_int : forall n, ~ IsInt v_false n.
Axiom v_None_not_int : forall n, ~ IsInt v_None n.
Axiom v_real_1_3_not_int : forall n, ~ IsInt v_real_1_3 n.
Axiom v_a_not_int : forall n, ~ IsInt v_a n.
Axiom v_b_not_int : forall n, ~ IsInt v_b n.
Axiom v_empty_list_not_int : forall n, ~ IsInt v_empty_list n.
Axiom v_empty_dict_not_int : forall n, ~ IsInt v_empty_dict n.
Axiom v_dict_a1_not_int : forall n, ~ IsInt v_dict_a1 n.
Axiom v_list_34_not_int : forall n, ~ IsInt v_list_34 n.
Axiom v_list_56_7_not_int : forall n, ~ IsInt v_list_56_7 n.

Axiom IsInt_v_5 : IsInt v_5 5%Z.
Axiom IsInt_v_neg7 : IsInt v_neg7 (-7)%Z.
Axiom IsInt_v_0 : IsInt v_0 0%Z.

Example test_case_complex:
  filter_integers_spec
    [v_true; v_false; v_None; v_real_1_3; v_5; v_neg7; v_0; v_a; v_b; v_empty_list; v_empty_dict; v_dict_a1; v_list_34; v_list_56_7]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_true_not_int |].
  eapply fir_cons_nonint; [apply v_false_not_int |].
  eapply fir_cons_nonint; [apply v_None_not_int |].
  eapply fir_cons_nonint; [apply v_real_1_3_not_int |].
  eapply fir_cons_int; [apply IsInt_v_5 |].
  eapply fir_cons_int; [apply IsInt_v_neg7 |].
  eapply fir_cons_int; [apply IsInt_v_0 |].
  eapply fir_cons_nonint; [apply v_a_not_int |].
  eapply fir_cons_nonint; [apply v_b_not_int |].
  eapply fir_cons_nonint; [apply v_empty_list_not_int |].
  eapply fir_cons_nonint; [apply v_empty_dict_not_int |].
  eapply fir_cons_nonint; [apply v_dict_a1_not_int |].
  eapply fir_cons_nonint; [apply v_list_34_not_int |].
  eapply fir_cons_nonint; [apply v_list_56_7_not_int |].
  constructor.
Qed.