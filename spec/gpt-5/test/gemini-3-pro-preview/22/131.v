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

(* Parameters for the test case values *)
Parameter val_false : Any.
Parameter val_none : Any.
Parameter val_1_3 : Any.
Parameter val_5 : Any.
Parameter val_neg7 : Any.
Parameter val_0 : Any.
Parameter val_a : Any.
Parameter val_b : Any.
Parameter val_nil : Any.
Parameter val_empty_dict : Any.
Parameter val_dict_mixed : Any.
Parameter val_list_3_4 : Any.

(* Axioms defining which values are integers and which are not *)
Axiom is_int_5 : IsInt val_5 5.
Axiom is_int_neg7 : IsInt val_neg7 (-7).
Axiom is_int_0 : IsInt val_0 0.

Axiom not_int_false : forall n, ~ IsInt val_false n.
Axiom not_int_none : forall n, ~ IsInt val_none n.
Axiom not_int_1_3 : forall n, ~ IsInt val_1_3 n.
Axiom not_int_a : forall n, ~ IsInt val_a n.
Axiom not_int_b : forall n, ~ IsInt val_b n.
Axiom not_int_nil : forall n, ~ IsInt val_nil n.
Axiom not_int_empty_dict : forall n, ~ IsInt val_empty_dict n.
Axiom not_int_dict_mixed : forall n, ~ IsInt val_dict_mixed n.
Axiom not_int_list_3_4 : forall n, ~ IsInt val_list_3_4 n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [val_false; val_false; val_none; val_1_3; val_5; val_neg7; val_0; val_a; val_b; val_nil; val_nil; val_empty_dict; val_dict_mixed; val_list_3_4; val_b] 
    [5; -7; 0].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_nonint. apply not_int_none.
  apply fir_cons_nonint. apply not_int_1_3.
  apply fir_cons_int with (n:=5). apply is_int_5.
  apply fir_cons_int with (n:=-7). apply is_int_neg7.
  apply fir_cons_int with (n:=0). apply is_int_0.
  apply fir_cons_nonint. apply not_int_a.
  apply fir_cons_nonint. apply not_int_b.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_empty_dict.
  apply fir_cons_nonint. apply not_int_dict_mixed.
  apply fir_cons_nonint. apply not_int_list_3_4.
  apply fir_cons_nonint. apply not_int_b.
  apply fir_nil.
Qed.