Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter val_real : R -> Any.
Axiom val_real_not_int : forall r n, ~ IsInt (val_real r) n.

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

Example test_filter_integers_reals : 
  filter_integers_spec 
    [val_real 2.7%R; val_real 1.5%R; val_real 2.8509645275834243%R; 
     val_real 2.212995480233853%R; val_real 2.5072599122885295%R; 
     val_real 2.8509645275834243%R; val_real 2.7%R] 
    [].
Proof.
  unfold filter_integers_spec.
  repeat (apply fir_cons_nonint; [ apply val_real_not_int | ]).
  apply fir_nil.
Qed.