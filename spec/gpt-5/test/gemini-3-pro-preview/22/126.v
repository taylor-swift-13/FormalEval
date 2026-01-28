Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

(* Parameters to represent the mixed types in the input list *)
Parameter any_bool : bool -> Any.
Parameter any_int : Z -> Any.
Parameter any_str : string -> Any.
Parameter any_none : Any.
Parameter any_float : Any. (* Abstract representation for 1.3 *)
Parameter any_list : list Any -> Any.
Parameter any_dict : Any. (* Abstract representation for dicts *)

(* Axioms defining IsInt behavior for these types *)
Axiom is_int_any_int : forall z, IsInt (any_int z) z.
Axiom not_int_bool : forall b n, ~ IsInt (any_bool b) n.
Axiom not_int_str : forall s n, ~ IsInt (any_str s) n.
Axiom not_int_none : forall n, ~ IsInt any_none n.
Axiom not_int_float : forall n, ~ IsInt any_float n.
Axiom not_int_list : forall l n, ~ IsInt (any_list l) n.
Axiom not_int_dict : forall n, ~ IsInt any_dict n.

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

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [any_bool true; any_bool false; any_none; any_float; 
     any_int 5; any_int (-7); any_int 1; 
     any_str "a"; any_str "b"; 
     any_list []; any_list []; 
     any_dict; any_dict; 
     any_list [any_int 3; any_int 4]; 
     any_list [any_int 5; any_int 6; any_str "7"]]
    [5; -7; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_bool.
  apply fir_cons_nonint. apply not_int_bool.
  apply fir_cons_nonint. apply not_int_none.
  apply fir_cons_nonint. apply not_int_float.
  apply fir_cons_int with (n := 5). apply is_int_any_int.
  apply fir_cons_int with (n := -7). apply is_int_any_int.
  apply fir_cons_int with (n := 1). apply is_int_any_int.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_nil.
Qed.