Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter InjInt : Z -> Any.
Parameter InjList : list Any -> Any.

Axiom IsInt_InjInt : forall z, IsInt (InjInt z) z.
Axiom NotIsInt_InjList : forall l n, ~ IsInt (InjList l) n.

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

Example test_filter_integers : 
  filter_integers_spec 
    [InjInt 1; InjList []; InjList []; InjInt 8; InjList [InjInt 5]; InjList [InjInt 8]; InjInt 9; InjInt 9; InjList []; InjList [InjInt 8]] 
    [1; 8; 9; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n:=1). apply IsInt_InjInt.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_cons_int with (n:=8). apply IsInt_InjInt.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_cons_int with (n:=9). apply IsInt_InjInt.
  apply fir_cons_int with (n:=9). apply IsInt_InjInt.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_cons_nonint. apply NotIsInt_InjList.
  apply fir_nil.
Qed.