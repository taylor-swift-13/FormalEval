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

(* Parameters representing the values in the input list:
   [1; []; []; 8; [5]; [7; 8]; 9; 9; []; [7; 8]] *)
Parameter v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Any.

(* Axioms defining which values are integers and which are not *)
Axiom ax_v1 : IsInt v1 1.
Axiom ax_v2 : forall n, ~ IsInt v2 n.
Axiom ax_v3 : forall n, ~ IsInt v3 n.
Axiom ax_v4 : IsInt v4 8.
Axiom ax_v5 : forall n, ~ IsInt v5 n.
Axiom ax_v6 : forall n, ~ IsInt v6 n.
Axiom ax_v7 : IsInt v7 9.
Axiom ax_v8 : IsInt v8 9.
Axiom ax_v9 : forall n, ~ IsInt v9 n.
Axiom ax_v10 : forall n, ~ IsInt v10 n.

Example test_filter_integers_complex : 
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] [1; 8; 9; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply ax_v1.
  apply fir_cons_nonint. apply ax_v2.
  apply fir_cons_nonint. apply ax_v3.
  apply fir_cons_int. apply ax_v4.
  apply fir_cons_nonint. apply ax_v5.
  apply fir_cons_nonint. apply ax_v6.
  apply fir_cons_int. apply ax_v7.
  apply fir_cons_int. apply ax_v8.
  apply fir_cons_nonint. apply ax_v9.
  apply fir_cons_nonint. apply ax_v10.
  apply fir_nil.
Qed.