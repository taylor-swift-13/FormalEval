Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inject_int : int -> Any.
Axiom IsInt_inject : forall n, IsInt (inject_int n) n.

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

Example test_filter_integers_1 : 
  filter_integers_spec 
    (map inject_int [1; -1; 0; 999; 999; 1]) 
    [1; -1; 0; 999; 999; 1].
Proof.
  unfold filter_integers_spec.
  simpl.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_cons_int. apply IsInt_inject.
  apply fir_nil.
Qed.