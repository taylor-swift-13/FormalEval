Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int : Type := Z.
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

Parameter v_true1 v_false1 v_none v_real13 v_5_any v_minus7_any v_0_any v_str_a v_str_bdef v_empty_list1 v_empty_list2 v_empty_dict v_dict_ab v_list_34 v_list_56_7str v_false2 : Any.

Axiom notint_v_true1 : forall n, ~ IsInt v_true1 n.
Axiom notint_v_false1 : forall n, ~ IsInt v_false1 n.
Axiom notint_v_none : forall n, ~ IsInt v_none n.
Axiom notint_v_real13 : forall n, ~ IsInt v_real13 n.
Axiom IsInt_v_5 : IsInt v_5_any (5%Z).
Axiom IsInt_v_minus7 : IsInt v_minus7_any ((-7)%Z).
Axiom IsInt_v_0 : IsInt v_0_any (0%Z).
Axiom notint_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom notint_v_str_bdef : forall n, ~ IsInt v_str_bdef n.
Axiom notint_v_empty_list1 : forall n, ~ IsInt v_empty_list1 n.
Axiom notint_v_empty_list2 : forall n, ~ IsInt v_empty_list2 n.
Axiom notint_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom notint_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom notint_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom notint_v_list_56_7str : forall n, ~ IsInt v_list_56_7str n.
Axiom notint_v_false2 : forall n, ~ IsInt v_false2 n.

Example test_case_mixed: filter_integers_spec
  [v_true1; v_false1; v_none; v_real13; v_5_any; v_minus7_any; v_0_any; v_str_a; v_str_bdef; v_empty_list1; v_empty_list2; v_empty_dict; v_dict_ab; v_list_34; v_list_56_7str; v_false2]
  [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply notint_v_true1|].
  eapply fir_cons_nonint; [apply notint_v_false1|].
  eapply fir_cons_nonint; [apply notint_v_none|].
  eapply fir_cons_nonint; [apply notint_v_real13|].
  eapply fir_cons_int; [apply IsInt_v_5|].
  eapply fir_cons_int; [apply IsInt_v_minus7|].
  eapply fir_cons_int; [apply IsInt_v_0|].
  eapply fir_cons_nonint; [apply notint_v_str_a|].
  eapply fir_cons_nonint; [apply notint_v_str_bdef|].
  eapply fir_cons_nonint; [apply notint_v_empty_list1|].
  eapply fir_cons_nonint; [apply notint_v_empty_list2|].
  eapply fir_cons_nonint; [apply notint_v_empty_dict|].
  eapply fir_cons_nonint; [apply notint_v_dict_ab|].
  eapply fir_cons_nonint; [apply notint_v_list_34|].
  eapply fir_cons_nonint; [apply notint_v_list_56_7str|].
  eapply fir_cons_nonint; [apply notint_v_false2|].
  constructor.
Qed.