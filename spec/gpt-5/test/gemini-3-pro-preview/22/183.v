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

(* Parameters for the test case values *)
Parameter v_1 v_9 : Any.
Parameter v_l1 v_l2 v_l3 v_l4 : Any.
Parameter i_1 i_9 : int.

(* Axioms defining which values are integers and which are not *)
Axiom is_int_v1 : IsInt v_1 i_1.
Axiom is_int_v9 : IsInt v_9 i_9.
Axiom not_int_vl1 : forall n, ~ IsInt v_l1 n.
Axiom not_int_vl2 : forall n, ~ IsInt v_l2 n.
Axiom not_int_vl3 : forall n, ~ IsInt v_l3 n.
Axiom not_int_vl4 : forall n, ~ IsInt v_l4 n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [v_1; v_l1; v_l2; v_l3; v_l4; v_9; v_1; v_1] 
    [i_1; i_9; i_1; i_1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := i_1). exact is_int_v1.
  apply fir_cons_nonint. exact not_int_vl1.
  apply fir_cons_nonint. exact not_int_vl2.
  apply fir_cons_nonint. exact not_int_vl3.
  apply fir_cons_nonint. exact not_int_vl4.
  apply fir_cons_int with (n := i_9). exact is_int_v9.
  apply fir_cons_int with (n := i_1). exact is_int_v1.
  apply fir_cons_int with (n := i_1). exact is_int_v1.
  apply fir_nil.
Qed.