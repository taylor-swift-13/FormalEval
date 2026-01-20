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

(* The test case input = [[]], output = [] means:
   - input is a list containing one element (an empty list, which is not an integer)
   - output is an empty list of integers
   
   We need to assume that there exists an Any value representing an empty list
   and that this value is not an integer. *)

Parameter empty_list_any : Any.
Axiom empty_list_not_int : forall n, ~ IsInt empty_list_any n.

Example test_filter_integers : filter_integers_spec [empty_list_any] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - exact empty_list_not_int.
  - apply fir_nil.
Qed.