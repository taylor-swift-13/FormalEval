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

Parameters list_4 list_5 val_8 : Any.
Axiom list_4_nonint : forall n, ~ IsInt list_4 n.
Axiom list_5_nonint : forall n, ~ IsInt list_5 n.
Axiom val_8_isint : IsInt val_8 8%Z.

Example test_case_nested_lists: filter_integers_spec [list_4; list_5; val_8] [8%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - exact list_4_nonint.
  - apply fir_cons_nonint.
    + exact list_5_nonint.
    + apply fir_cons_int.
      * exact val_8_isint.
      * apply fir_nil.
Qed.