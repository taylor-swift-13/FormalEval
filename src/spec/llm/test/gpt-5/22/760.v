Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Definition input_bools : list bool :=
  [true; false; true; true; false; true; true; false; true; false; true; true].

Parameter inj_list_bool : list bool -> Any.
Definition v_bools : Any := inj_list_bool input_bools.
Axiom v_bools_nonint : forall n, ~ IsInt v_bools n.

Example test_case_bools: filter_integers_spec [v_bools] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - exact v_bools_nonint.
  - apply fir_nil.
Qed.