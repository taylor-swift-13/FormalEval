Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_int : Z -> Any.
Parameter inj_other : nat -> Any.

Axiom IsInt_inj_int : forall z, IsInt (inj_int z) z.
Axiom IsInt_inj_other : forall k z, ~ IsInt (inj_other k) z.

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
    [inj_other 0; inj_other 0; inj_other 1; inj_other 2; 
     inj_int 5; inj_int (-7); inj_int 0; 
     inj_other 3; inj_other 4; inj_other 5; inj_other 5; 
     inj_other 6; inj_other 7; inj_other 8; inj_other 9] 
    [5; -7; 0].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_int. apply IsInt_inj_int.
  apply fir_cons_int. apply IsInt_inj_int.
  apply fir_cons_int. apply IsInt_inj_int.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_cons_nonint. apply IsInt_inj_other.
  apply fir_nil.
Qed.