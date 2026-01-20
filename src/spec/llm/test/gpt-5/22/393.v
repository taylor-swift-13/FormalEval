Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter v_false1 : Any.
Parameter v_false2 : Any.
Parameter v_none1 : Any.
Parameter v_real1 : Any.
Parameter v_5 : Any.
Parameter v_neg7 : Any.
Parameter v_0 : Any.
Parameter v_none2 : Any.
Parameter v_a_str : Any.
Parameter v_b_str : Any.
Parameter v_empty_list1 : Any.
Parameter v_empty_list2 : Any.
Parameter v_empty_dict : Any.
Parameter v_neg46 : Any.
Parameter v_dict_ab : Any.
Parameter v_list_34 : Any.
Parameter v_list_56_7 : Any.

Axiom v_false1_nonint : forall n, ~ IsInt v_false1 n.
Axiom v_false2_nonint : forall n, ~ IsInt v_false2 n.
Axiom v_none1_nonint : forall n, ~ IsInt v_none1 n.
Axiom v_real1_nonint : forall n, ~ IsInt v_real1 n.
Axiom v_none2_nonint : forall n, ~ IsInt v_none2 n.
Axiom v_a_str_nonint : forall n, ~ IsInt v_a_str n.
Axiom v_b_str_nonint : forall n, ~ IsInt v_b_str n.
Axiom v_empty_list1_nonint : forall n, ~ IsInt v_empty_list1 n.
Axiom v_empty_list2_nonint : forall n, ~ IsInt v_empty_list2 n.
Axiom v_empty_dict_nonint : forall n, ~ IsInt v_empty_dict n.
Axiom v_dict_ab_nonint : forall n, ~ IsInt v_dict_ab n.
Axiom v_list_34_nonint : forall n, ~ IsInt v_list_34 n.
Axiom v_list_56_7_nonint : forall n, ~ IsInt v_list_56_7 n.

Axiom v_5_isint : IsInt v_5 5%Z.
Axiom v_neg7_isint : IsInt v_neg7 (-7)%Z.
Axiom v_0_isint : IsInt v_0 0%Z.
Axiom v_neg46_isint : IsInt v_neg46 (-46)%Z.

Example test_case: filter_integers_spec
  [v_false1; v_false2; v_none1; v_real1; v_5; v_neg7; v_0; v_none2; v_a_str; v_b_str; v_empty_list1; v_empty_list2; v_empty_dict; v_neg46; v_dict_ab; v_list_34; v_list_56_7]
  [5%Z; (-7)%Z; 0%Z; (-46)%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_false1_nonint |].
  eapply fir_cons_nonint; [apply v_false2_nonint |].
  eapply fir_cons_nonint; [apply v_none1_nonint |].
  eapply fir_cons_nonint; [apply v_real1_nonint |].
  eapply fir_cons_int; [apply v_5_isint |].
  eapply fir_cons_int; [apply v_neg7_isint |].
  eapply fir_cons_int; [apply v_0_isint |].
  eapply fir_cons_nonint; [apply v_none2_nonint |].
  eapply fir_cons_nonint; [apply v_a_str_nonint |].
  eapply fir_cons_nonint; [apply v_b_str_nonint |].
  eapply fir_cons_nonint; [apply v_empty_list1_nonint |].
  eapply fir_cons_nonint; [apply v_empty_list2_nonint |].
  eapply fir_cons_nonint; [apply v_empty_dict_nonint |].
  eapply fir_cons_int; [apply v_neg46_isint |].
  eapply fir_cons_nonint; [apply v_dict_ab_nonint |].
  eapply fir_cons_nonint; [apply v_list_34_nonint |].
  eapply fir_cons_nonint; [apply v_list_56_7_nonint |].
  constructor.
Qed.