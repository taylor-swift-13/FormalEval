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

Parameter mk_int : Z -> Any.
Parameter mk_other : nat -> Any.

Axiom IsInt_mk_int : forall z, IsInt (mk_int z) z.
Axiom Not_IsInt_mk_other : forall k n, ~ IsInt (mk_other k) n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [mk_int 1; mk_other 0; mk_other 1; mk_int 8; mk_other 2; mk_other 3; mk_int 9; mk_int 9; mk_other 4]
    [1; 8; 9; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply IsInt_mk_int.
  apply fir_cons_nonint. apply Not_IsInt_mk_other.
  apply fir_cons_nonint. apply Not_IsInt_mk_other.
  apply fir_cons_int. apply IsInt_mk_int.
  apply fir_cons_nonint. apply Not_IsInt_mk_other.
  apply fir_cons_nonint. apply Not_IsInt_mk_other.
  apply fir_cons_int. apply IsInt_mk_int.
  apply fir_cons_int. apply IsInt_mk_int.
  apply fir_cons_nonint. apply Not_IsInt_mk_other.
  apply fir_nil.
Qed.