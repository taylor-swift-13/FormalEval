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

Parameter a1_1Z a2_list_2_3 a3_4Z a4_list_5 a5_empty_list a6_list_7_str8 a7_str9 a8_obj_empty a9_1Z : Any.
Axiom a1_isint : IsInt a1_1Z 1%Z.
Axiom a3_isint : IsInt a3_4Z 4%Z.
Axiom a9_isint : IsInt a9_1Z 1%Z.
Axiom a2_nonint : forall n, ~ IsInt a2_list_2_3 n.
Axiom a4_nonint : forall n, ~ IsInt a4_list_5 n.
Axiom a5_nonint : forall n, ~ IsInt a5_empty_list n.
Axiom a6_nonint : forall n, ~ IsInt a6_list_7_str8 n.
Axiom a7_nonint : forall n, ~ IsInt a7_str9 n.
Axiom a8_nonint : forall n, ~ IsInt a8_obj_empty n.

Example test_case_nested: filter_integers_spec [a1_1Z; a2_list_2_3; a3_4Z; a4_list_5; a5_empty_list; a6_list_7_str8; a7_str9; a8_obj_empty; a9_1Z] [1%Z; 4%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact a1_isint|].
  eapply fir_cons_nonint; [exact a2_nonint|].
  eapply fir_cons_int; [exact a3_isint|].
  eapply fir_cons_nonint; [exact a4_nonint|].
  eapply fir_cons_nonint; [exact a5_nonint|].
  eapply fir_cons_nonint; [exact a6_nonint|].
  eapply fir_cons_nonint; [exact a7_nonint|].
  eapply fir_cons_nonint; [exact a8_nonint|].
  eapply fir_cons_int; [exact a9_isint|].
  constructor.
Qed.