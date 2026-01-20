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

Parameter a_false a_None a_real_1_3 a_5 a_minus7 a_0 a_str_a a_str_b a_list_empty1 a_list_empty2 a_list_4 a_obj_empty a_dict_ab a_list_4_2 a_list_5_6_str7 : Any.

Axiom IsInt_a_5 : IsInt a_5 5%Z.
Axiom IsInt_a_minus7 : IsInt a_minus7 (-7)%Z.
Axiom IsInt_a_0 : IsInt a_0 0%Z.

Axiom NonInt_a_false : forall n, ~ IsInt a_false n.
Axiom NonInt_a_None : forall n, ~ IsInt a_None n.
Axiom NonInt_a_real_1_3 : forall n, ~ IsInt a_real_1_3 n.
Axiom NonInt_a_str_a : forall n, ~ IsInt a_str_a n.
Axiom NonInt_a_str_b : forall n, ~ IsInt a_str_b n.
Axiom NonInt_a_list_empty1 : forall n, ~ IsInt a_list_empty1 n.
Axiom NonInt_a_list_empty2 : forall n, ~ IsInt a_list_empty2 n.
Axiom NonInt_a_list_4 : forall n, ~ IsInt a_list_4 n.
Axiom NonInt_a_obj_empty : forall n, ~ IsInt a_obj_empty n.
Axiom NonInt_a_dict_ab : forall n, ~ IsInt a_dict_ab n.
Axiom NonInt_a_list_4_2 : forall n, ~ IsInt a_list_4_2 n.
Axiom NonInt_a_list_5_6_str7 : forall n, ~ IsInt a_list_5_6_str7 n.

Example test_case_mixed:
  filter_integers_spec
    [a_false; a_None; a_real_1_3; a_5; a_minus7; a_0; a_str_a; a_str_b; a_list_empty1; a_list_empty2; a_list_4; a_obj_empty; a_dict_ab; a_list_4_2; a_list_5_6_str7]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_a_false |].
  eapply fir_cons_nonint; [apply NonInt_a_None |].
  eapply fir_cons_nonint; [apply NonInt_a_real_1_3 |].
  eapply fir_cons_int with (n:=5%Z); [apply IsInt_a_5 |].
  eapply fir_cons_int with (n:=(-7)%Z); [apply IsInt_a_minus7 |].
  eapply fir_cons_int with (n:=0%Z); [apply IsInt_a_0 |].
  eapply fir_cons_nonint; [apply NonInt_a_str_a |].
  eapply fir_cons_nonint; [apply NonInt_a_str_b |].
  eapply fir_cons_nonint; [apply NonInt_a_list_empty1 |].
  eapply fir_cons_nonint; [apply NonInt_a_list_empty2 |].
  eapply fir_cons_nonint; [apply NonInt_a_list_4 |].
  eapply fir_cons_nonint; [apply NonInt_a_obj_empty |].
  eapply fir_cons_nonint; [apply NonInt_a_dict_ab |].
  eapply fir_cons_nonint; [apply NonInt_a_list_4_2 |].
  eapply fir_cons_nonint; [apply NonInt_a_list_5_6_str7 |].
  constructor.
Qed.