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

Parameter inj_int : Z -> Any.
Parameter inj_other : list Z -> Any.

Axiom inj_int_is_int : forall z, IsInt (inj_int z) z.
Axiom inj_other_not_int : forall l z, ~ IsInt (inj_other l) z.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [inj_int 1; inj_other [4]; inj_other [5]; inj_int 9; inj_other [5]] 
    [1; 9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1).
  - apply inj_int_is_int.
  - apply fir_cons_nonint.
    + apply inj_other_not_int.
    + apply fir_cons_nonint.
      * apply inj_other_not_int.
      * apply fir_cons_int with (n := 9).
        -- apply inj_int_is_int.
        -- apply fir_cons_nonint.
           ++ apply inj_other_not_int.
           ++ apply fir_nil.
Qed.