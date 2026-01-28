Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter mk_int : Z -> Any.
Parameter mk_other : nat -> Any.

Axiom is_int_mk_int : forall z, IsInt (mk_int z) z.
Axiom not_is_int_mk_other : forall k n, ~ IsInt (mk_other k) n.

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

Example test_filter_integers_complex : 
  filter_integers_spec 
    [mk_other 0; mk_other 1; mk_other 2; mk_other 3; mk_int 5; mk_other 4; mk_int (-7); mk_int 0; 
     mk_other 5; mk_other 6; mk_other 7; mk_other 8; mk_other 9; mk_other 10; mk_other 11; mk_other 12] 
    [5; -7; 0].
Proof.
  unfold filter_integers_spec.
  repeat (
    match goal with
    | [ |- filter_integers_rel [] [] ] => apply fir_nil
    | [ |- filter_integers_rel (mk_int ?z :: _) (?z :: _) ] =>
        apply fir_cons_int; [ apply is_int_mk_int | ]
    | [ |- filter_integers_rel (mk_other _ :: _) _ ] =>
        apply fir_cons_nonint; [ apply not_is_int_mk_other | ]
    end).
Qed.