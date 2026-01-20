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

Parameter a_true a_false a_real a_5 a_m7 a_0 a_str_a a_str_b a_empty_list1 a_empty_list2 a_empty_dict a_dict_ab a_list_34 a_list_56s : Any.

Parameter notint_true : forall n, ~ IsInt a_true n.
Parameter notint_false : forall n, ~ IsInt a_false n.
Parameter notint_real : forall n, ~ IsInt a_real n.
Parameter notint_str_a : forall n, ~ IsInt a_str_a n.
Parameter notint_str_b : forall n, ~ IsInt a_str_b n.
Parameter notint_empty_list1 : forall n, ~ IsInt a_empty_list1 n.
Parameter notint_empty_list2 : forall n, ~ IsInt a_empty_list2 n.
Parameter notint_empty_dict : forall n, ~ IsInt a_empty_dict n.
Parameter notint_dict_ab : forall n, ~ IsInt a_dict_ab n.
Parameter notint_list_34 : forall n, ~ IsInt a_list_34 n.
Parameter notint_list_56s : forall n, ~ IsInt a_list_56s n.

Parameter isint_5 : IsInt a_5 5%Z.
Parameter isint_m7 : IsInt a_m7 (-7)%Z.
Parameter isint_0 : IsInt a_0 0%Z.

Example test_case_mixed:
  filter_integers_spec
    [a_true; a_false; a_real; a_5; a_m7; a_0; a_str_a; a_str_b; a_empty_list1; a_empty_list2; a_empty_dict; a_dict_ab; a_list_34; a_list_56s]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply notint_true|].
  eapply fir_cons_nonint; [apply notint_false|].
  eapply fir_cons_nonint; [apply notint_real|].
  eapply (fir_cons_int a_5 5%Z); [apply isint_5|].
  eapply (fir_cons_int a_m7 (-7)%Z); [apply isint_m7|].
  eapply (fir_cons_int a_0 0%Z); [apply isint_0|].
  eapply fir_cons_nonint; [apply notint_str_a|].
  eapply fir_cons_nonint; [apply notint_str_b|].
  eapply fir_cons_nonint; [apply notint_empty_list1|].
  eapply fir_cons_nonint; [apply notint_empty_list2|].
  eapply fir_cons_nonint; [apply notint_empty_dict|].
  eapply fir_cons_nonint; [apply notint_dict_ab|].
  eapply fir_cons_nonint; [apply notint_list_34|].
  eapply fir_cons_nonint; [apply notint_list_56s|].
  constructor.
Qed.