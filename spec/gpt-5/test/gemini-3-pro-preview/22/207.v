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

Parameter v_nil : Any.
Parameter v_l6 : Any.
Parameter v_l78 : Any.
Parameter v_9 : Any.

Axiom not_int_nil : forall n, ~ IsInt v_nil n.
Axiom not_int_l6 : forall n, ~ IsInt v_l6 n.
Axiom not_int_l78 : forall n, ~ IsInt v_l78 n.
Axiom is_int_9 : IsInt v_9 9.

Example test_filter_integers : 
  filter_integers_spec 
    [v_nil; v_nil; v_l6; v_l78; v_9; v_l6] 
    [9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. exact not_int_nil.
  apply fir_cons_nonint. exact not_int_nil.
  apply fir_cons_nonint. exact not_int_l6.
  apply fir_cons_nonint. exact not_int_l78.
  apply fir_cons_int with (n := 9). exact is_int_9.
  apply fir_cons_nonint. exact not_int_l6.
  apply fir_nil.
Qed.