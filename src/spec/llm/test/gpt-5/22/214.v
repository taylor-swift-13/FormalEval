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

Parameter a_list4_left : Any.
Parameter a_list4_right : Any.
Parameter a_8 : Any.

Axiom a_list4_left_nonint : forall n, ~ IsInt a_list4_left n.
Axiom a_list4_right_nonint : forall n, ~ IsInt a_list4_right n.
Axiom a_8_is_int : IsInt a_8 8%Z.

Example test_case_nested: filter_integers_spec [a_list4_left; a_8; a_list4_right] [8%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - exact a_list4_left_nonint.
  - apply fir_cons_int with (n:=8%Z).
    + exact a_8_is_int.
    + apply fir_cons_nonint.
      * exact a_list4_right_nonint.
      * apply fir_nil.
Qed.