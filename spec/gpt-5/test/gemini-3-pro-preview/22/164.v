Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter v_list_4 : Any.
Parameter v_list_5 : Any.
Parameter v_8 : Any.

Axiom not_int_v_list_4 : forall n, ~ IsInt v_list_4 n.
Axiom not_int_v_list_5 : forall n, ~ IsInt v_list_5 n.
Axiom is_int_v_8 : IsInt v_8 8.

Example test_filter_integers_mixed : filter_integers_spec [v_list_4; v_list_5; v_8] [8].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply not_int_v_list_4.
  - apply fir_cons_nonint.
    + apply not_int_v_list_5.
    + apply fir_cons_int with (n := 8).
      * apply is_int_v_8.
      * apply fir_nil.
Qed.