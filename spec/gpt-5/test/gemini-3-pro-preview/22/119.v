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

(* Parameters representing the specific input values for the test case *)
Parameter val_1 : Any.           (* 1 *)
Parameter val_list_4 : Any.      (* [4] *)
Parameter val_list_5 : Any.      (* [5] *)
Parameter val_list_788 : Any.    (* [7; 8; 8] *)
Parameter val_9 : Any.           (* 9 *)

(* Axioms defining which values are integers *)
Axiom is_int_val_1 : IsInt val_1 1.
Axiom not_int_val_list_4 : forall n, ~ IsInt val_list_4 n.
Axiom not_int_val_list_5 : forall n, ~ IsInt val_list_5 n.
Axiom not_int_val_list_788 : forall n, ~ IsInt val_list_788 n.
Axiom is_int_val_9 : IsInt val_9 9.

Example test_filter_integers_mixed : 
  filter_integers_spec [val_1; val_list_4; val_list_5; val_list_788; val_9] [1; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply is_int_val_1.
  - apply fir_cons_nonint.
    + apply not_int_val_list_4.
    + apply fir_cons_nonint.
      * apply not_int_val_list_5.
      * apply fir_cons_nonint.
        -- apply not_int_val_list_788.
        -- apply fir_cons_int with (n := 9).
           ++ apply is_int_val_9.
           ++ apply fir_nil.
Qed.