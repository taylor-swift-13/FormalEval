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

Parameter list_str_5_a : Any.
Parameter list_str_5_b : Any.
Parameter any_7 : Any.
Parameter list_2_and_str_3 : Any.

Axiom H_nonint_1 : forall n, ~ IsInt list_str_5_a n.
Axiom H_nonint_2 : forall n, ~ IsInt list_str_5_b n.
Axiom H_isint_7 : IsInt any_7 7%Z.
Axiom H_nonint_4 : forall n, ~ IsInt list_2_and_str_3 n.

Example test_case_new: filter_integers_spec [list_str_5_a; list_str_5_b; any_7; list_2_and_str_3] [7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact H_nonint_1|].
  eapply fir_cons_nonint; [exact H_nonint_2|].
  eapply fir_cons_int; [exact H_isint_7|].
  eapply fir_cons_nonint; [exact H_nonint_4|].
  constructor.
Qed.